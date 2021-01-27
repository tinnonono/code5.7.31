/*****************************************************************************

Copyright (c) 1995, 2019, Oracle and/or its affiliates. All Rights Reserved.

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License, version 2.0,
as published by the Free Software Foundation.

This program is also distributed with certain software (including
but not limited to OpenSSL) that is licensed under separate terms,
as designated in a particular file or component or in included license
documentation.  The authors of MySQL hereby grant you an additional
permission to link the program and your derivative works with the
separately licensed software that they have included with MySQL.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License, version 2.0, for more details.

You should have received a copy of the GNU General Public License along with
this program; if not, write to the Free Software Foundation, Inc.,
51 Franklin Street, Suite 500, Boston, MA 02110-1335 USA

*****************************************************************************/

/**************************************************//**
@file buf/buf0flu.cc
The database buffer buf_pool flush algorithm

Created 11/11/1995 Heikki Tuuri
*******************************************************/

#include "ha_prototypes.h"
#include <mysql/service_thd_wait.h>
#include <my_dbug.h>

#include "buf0flu.h"

#ifdef UNIV_NONINL
#include "buf0flu.ic"
#endif

#include "buf0buf.h"
#include "buf0checksum.h"
#include "srv0start.h"
#include "srv0srv.h"
#include "page0zip.h"
#ifndef UNIV_HOTBACKUP
#include "ut0byte.h"
#include "page0page.h"
#include "fil0fil.h"
#include "buf0lru.h"
#include "buf0rea.h"
#include "ibuf0ibuf.h"
#include "log0log.h"
#include "os0file.h"
#include "trx0sys.h"
#include "srv0mon.h"
#include "fsp0sysspace.h"
#include "ut0stage.h"

#ifdef UNIV_LINUX
/* include defs for CPU time priority settings */
#include <unistd.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <sys/resource.h>
static const int buf_flush_page_cleaner_priority = -20;
#endif /* UNIV_LINUX */

/** Sleep time in microseconds for loop waiting for the oldest
modification lsn */
static const ulint buf_flush_wait_flushed_sleep_time = 10000;

/** Number of pages flushed through non flush_list flushes. */
static ulint buf_lru_flush_page_count = 0;

/** Flag indicating if the page_cleaner is in active state. This flag
is set to TRUE by the page_cleaner thread when it is spawned and is set
back to FALSE at shutdown by the page_cleaner as well. Therefore no
need to protect it by a mutex. It is only ever read by the thread
doing the shutdown */
bool buf_page_cleaner_is_active = false;

/** Factor for scan length to determine n_pages for intended oldest LSN
progress */
static ulint buf_flush_lsn_scan_factor = 3;

/** Average redo generation rate */
static lsn_t lsn_avg_rate = 0;

/** Target oldest LSN for the requested flush_sync */
static lsn_t buf_flush_sync_lsn = 0;

#ifdef UNIV_PFS_THREAD
mysql_pfs_key_t page_cleaner_thread_key;
#endif /* UNIV_PFS_THREAD */

/** Event to synchronise with the flushing. */
os_event_t	buf_flush_event;

/** State for page cleaner array slot */
enum page_cleaner_state_t {
	/** Not requested any yet.
	Moved from FINISHED by the coordinator. */
	PAGE_CLEANER_STATE_NONE = 0,
	/** Requested but not started flushing.
	Moved from NONE by the coordinator. */
	PAGE_CLEANER_STATE_REQUESTED,
	/** Flushing is on going.
	Moved from REQUESTED by the worker. */
	PAGE_CLEANER_STATE_FLUSHING,
	/** Flushing was finished.
	Moved from FLUSHING by the worker. */
	PAGE_CLEANER_STATE_FINISHED
};

/** Page cleaner request state for each buffer pool instance */
/* 
	每个buffer instance都包含一个这样的结构体，page clean工作线程刷新的时候每个线程都会轮询的检测每个槽，
	直到找到没有被其他page clean线程刷新的槽进行刷新工作或者所有的槽（buffer instance ）都刷新完成为止。
*/
struct page_cleaner_slot_t {
	/* 状态PAGE_CLEANER_STATE_REQUESTED、PAGE_CLEANER_STATE_FLUSHING和PAGE_CLEANER_STATE_FINISHED中的一种 */
	page_cleaner_state_t	state;	/*!< state of the request.
					protected by page_cleaner_t::mutex
					if the worker thread got the slot and
					set to PAGE_CLEANER_STATE_FLUSHING,
					n_flushed_lru and n_flushed_list can be
					updated only by the worker thread */
	/* This value is set during state==PAGE_CLEANER_STATE_NONE */
	/* 本槽需要刷新的总的块数量 */
	ulint			n_pages_requested;
					/*!< number of requested pages
					for the slot */
	/* These values are updated during state==PAGE_CLEANER_STATE_FLUSHING,
	and commited with state==PAGE_CLEANER_STATE_FINISHED.
	The consistency is protected by the 'state' */
	ulint			n_flushed_lru;
					/*!< number of flushed pages
					by LRU scan flushing */
	/* 已经刷新的块数  */				
	ulint			n_flushed_list;
					/*!< number of flushed pages
					by flush_list flushing */
	/* 布尔值，刷新是否完成 */				
	bool			succeeded_list;
					/*!< true if flush_list flushing
					succeeded. */
	/* 本槽刷新消耗的时间（累计参考pc_flush_slot函数） */				
	uint64_t		flush_lru_time;
					/*!< elapsed time for LRU flushing */				
	uint64_t		flush_list_time;
					/*!< elapsed time for flush_list
					flushing */
	/* 本槽进行刷新操作的次数（累计参考pc_flush_slot函数） */
	ulint			flush_lru_pass;
					/*!< count to attempt LRU flushing */
	ulint			flush_list_pass;
					/*!< count to attempt flush_list
					flushing */
};

/** Page cleaner structure common for all threads */
/* 整个Innodb只有一个，包含整个page clean线程相关信息。其中包含了一个page_cleaner_slot_t的指针。 */
struct page_cleaner_t {
	/* 用于保护整个page_cleaner_t结构体和page_cleaner_slot_t结构体，当需要修改结构体信息的时候需要获取这个mutex， 如在pc_request函数中 */
	ib_mutex_t		mutex;		/*!< mutex to protect whole of
						page_cleaner_t struct and
						page_cleaner_slot_t slots. */
	/* 一个条件变量，用于唤醒堵塞在这个条件之上的工作线程  */
	os_event_t		is_requested;	/*!< event to activate worker
						threads. */
	/*  一个条件变量，用于通知协调线程刷新工作已经完成 */					
	os_event_t		is_finished;	/*!< event to signal that all
						slots were finished. */
	/* 当前存在的工作线程总数 */					
	volatile ulint		n_workers;	/*!< number of worker threads
						in existence */
	/* 布尔值，当前是否需要进行脏数据刷新工作 */					
	bool			requested;	/*!< true if requested pages
						to flush */
	/* 需要刷新到lsn的位置，当需要同步刷新的时候，这个值将被赋予，以保证小于这个lsn的日志都已经完成了刷盘工作 */					
	lsn_t			lsn_limit;	/*!< upper limit of LSN to be
						flushed */
	/* 槽的数量，槽的数量和buffer instance的数量相同 */					
	ulint			n_slots;	/*!< total number of slots */
	/* 当前处于需要刷新状态下(PAGE_CLEANER_STATE_REQUESTED)的槽的数量 */
	ulint			n_slots_requested;
						/*!< number of slots
						in the state
						PAGE_CLEANER_STATE_REQUESTED */
	/* 当前处于刷新状态下(PAGE_CLEANER_STATE_FLUSHING)的槽的数量 */					
	ulint			n_slots_flushing;
						/*!< number of slots
						in the state
						PAGE_CLEANER_STATE_FLUSHING */
	/* 当前处于已经刷新完成状态下(PAGE_CLEANER_STATE_FINISHED)的槽的数量  */					
	ulint			n_slots_finished;
						/*!< number of slots
						in the state
						PAGE_CLEANER_STATE_FINISHED */
	/* 整个(以innodb buffer为单位)刷新消耗的时间（累计 page_cleaner->flush_time += ut_time_ms() - tm;） */					
	uint64_t		flush_time;	/*!< elapsed time to flush
						requests for all slots */
	/* 整个(以innodb buffer为单位)刷新的次数（累计 page_cleaner->flush_pass++;） */					
	ulint			flush_pass;	/*!< count to finish to flush
						requests for all slots */
	/* 指针指向实际的槽 */					
	page_cleaner_slot_t*	slots;		/*!< pointer to the slots */
	/* 布尔值，如果关闭innodb会被设置为false，进行强行刷新脏数据 */
	bool			is_running;	/*!< false if attempt
						to shutdown */

#ifdef UNIV_DEBUG
	ulint			n_disabled_debug;
						/*<! how many of pc threads
						have been disabled */
#endif /* UNIV_DEBUG */
};

static page_cleaner_t*	page_cleaner = NULL;

#ifdef UNIV_DEBUG
my_bool innodb_page_cleaner_disabled_debug;
#endif /* UNIV_DEBUG */

/** If LRU list of a buf_pool is less than this size then LRU eviction
should not happen. This is because when we do LRU flushing we also put
the blocks on free list. If LRU list is very small then we can end up
in thrashing. */
#define BUF_LRU_MIN_LEN		256

/* @} */

/******************************************************************//**
Increases flush_list size in bytes with the page size in inline function */
static inline
void
incr_flush_list_size_in_bytes(
/*==========================*/
	buf_block_t*	block,		/*!< in: control block */
	buf_pool_t*	buf_pool)	/*!< in: buffer pool instance */
{
	ut_ad(buf_flush_list_mutex_own(buf_pool));

	buf_pool->stat.flush_list_bytes += block->page.size.physical();

	ut_ad(buf_pool->stat.flush_list_bytes <= buf_pool->curr_pool_size);
}

#if defined UNIV_DEBUG || defined UNIV_BUF_DEBUG
/******************************************************************//**
Validates the flush list.
@return TRUE if ok */
static
ibool
buf_flush_validate_low(
/*===================*/
	buf_pool_t*	buf_pool);	/*!< in: Buffer pool instance */

/******************************************************************//**
Validates the flush list some of the time.
@return TRUE if ok or the check was skipped */
static
ibool
buf_flush_validate_skip(
/*====================*/
	buf_pool_t*	buf_pool)	/*!< in: Buffer pool instance */
{
/** Try buf_flush_validate_low() every this many times */
# define BUF_FLUSH_VALIDATE_SKIP	23

	/** The buf_flush_validate_low() call skip counter.
	Use a signed type because of the race condition below. */
	static int buf_flush_validate_count = BUF_FLUSH_VALIDATE_SKIP;

	/* There is a race condition below, but it does not matter,
	because this call is only for heuristic purposes. We want to
	reduce the call frequency of the costly buf_flush_validate_low()
	check in debug builds. */
	if (--buf_flush_validate_count > 0) {
		return(TRUE);
	}

	buf_flush_validate_count = BUF_FLUSH_VALIDATE_SKIP;
	return(buf_flush_validate_low(buf_pool));
}
#endif /* UNIV_DEBUG || UNIV_BUF_DEBUG */

/******************************************************************//**
Insert a block in the flush_rbt and returns a pointer to its
predecessor or NULL if no predecessor. The ordering is maintained
on the basis of the <oldest_modification, space, offset> key.
@return pointer to the predecessor or NULL if no predecessor. */
static
buf_page_t*
buf_flush_insert_in_flush_rbt(
/*==========================*/
	buf_page_t*	bpage)	/*!< in: bpage to be inserted. */
{
	const ib_rbt_node_t*	c_node;
	const ib_rbt_node_t*	p_node;
	buf_page_t*		prev = NULL;
	buf_pool_t*		buf_pool = buf_pool_from_bpage(bpage);

	ut_ad(buf_flush_list_mutex_own(buf_pool));

	/* Insert this buffer into the rbt. */
	c_node = rbt_insert(buf_pool->flush_rbt, &bpage, &bpage);
	ut_a(c_node != NULL);

	/* Get the predecessor. */
	p_node = rbt_prev(buf_pool->flush_rbt, c_node);

	if (p_node != NULL) {
		buf_page_t**	value;
		value = rbt_value(buf_page_t*, p_node);
		prev = *value;
		ut_a(prev != NULL);
	}

	return(prev);
}

/*********************************************************//**
Delete a bpage from the flush_rbt. */
static
void
buf_flush_delete_from_flush_rbt(
/*============================*/
	buf_page_t*	bpage)	/*!< in: bpage to be removed. */
{
#ifdef UNIV_DEBUG
	ibool		ret = FALSE;
#endif /* UNIV_DEBUG */
	buf_pool_t*	buf_pool = buf_pool_from_bpage(bpage);

	ut_ad(buf_flush_list_mutex_own(buf_pool));

#ifdef UNIV_DEBUG
	ret =
#endif /* UNIV_DEBUG */
	rbt_delete(buf_pool->flush_rbt, &bpage);

	ut_ad(ret);
}

/*****************************************************************//**
Compare two modified blocks in the buffer pool. The key for comparison
is:
key = <oldest_modification, space, offset>
This comparison is used to maintian ordering of blocks in the
buf_pool->flush_rbt.
Note that for the purpose of flush_rbt, we only need to order blocks
on the oldest_modification. The other two fields are used to uniquely
identify the blocks.
@return < 0 if b2 < b1, 0 if b2 == b1, > 0 if b2 > b1 */
static
int
buf_flush_block_cmp(
/*================*/
	const void*	p1,		/*!< in: block1 */
	const void*	p2)		/*!< in: block2 */
{
	int			ret;
	const buf_page_t*	b1 = *(const buf_page_t**) p1;
	const buf_page_t*	b2 = *(const buf_page_t**) p2;

	ut_ad(b1 != NULL);
	ut_ad(b2 != NULL);

#ifdef UNIV_DEBUG
	buf_pool_t*	buf_pool = buf_pool_from_bpage(b1);
#endif /* UNIV_DEBUG */

	ut_ad(buf_flush_list_mutex_own(buf_pool));

	ut_ad(b1->in_flush_list);
	ut_ad(b2->in_flush_list);

	if (b2->oldest_modification > b1->oldest_modification) {
		return(1);
	} else if (b2->oldest_modification < b1->oldest_modification) {
		return(-1);
	}

	/* If oldest_modification is same then decide on the space. */
	ret = (int)(b2->id.space() - b1->id.space());

	/* Or else decide ordering on the page number. */
	return(ret ? ret : (int) (b2->id.page_no() - b1->id.page_no()));
}

/********************************************************************//**
Initialize the red-black tree to speed up insertions into the flush_list
during recovery process. Should be called at the start of recovery
process before any page has been read/written. */
void
buf_flush_init_flush_rbt(void)
/*==========================*/
{
	ulint	i;

	for (i = 0; i < srv_buf_pool_instances; i++) {
		buf_pool_t*	buf_pool;

		buf_pool = buf_pool_from_array(i);

		buf_flush_list_mutex_enter(buf_pool);

		ut_ad(buf_pool->flush_rbt == NULL);

		/* Create red black tree for speedy insertions in flush list. */
		buf_pool->flush_rbt = rbt_create(
			sizeof(buf_page_t*), buf_flush_block_cmp);

		buf_flush_list_mutex_exit(buf_pool);
	}
}

/********************************************************************//**
Frees up the red-black tree. */
void
buf_flush_free_flush_rbt(void)
/*==========================*/
{
	ulint	i;

	for (i = 0; i < srv_buf_pool_instances; i++) {
		buf_pool_t*	buf_pool;

		buf_pool = buf_pool_from_array(i);

		buf_flush_list_mutex_enter(buf_pool);

#if defined UNIV_DEBUG || defined UNIV_BUF_DEBUG
		ut_a(buf_flush_validate_low(buf_pool));
#endif /* UNIV_DEBUG || UNIV_BUF_DEBUG */

		rbt_free(buf_pool->flush_rbt);
		buf_pool->flush_rbt = NULL;

		buf_flush_list_mutex_exit(buf_pool);
	}
}

/********************************************************************//**
Inserts a modified block into the flush list. */
void
buf_flush_insert_into_flush_list(
/*=============================*/
	buf_pool_t*	buf_pool,	/*!< buffer pool instance */
	buf_block_t*	block,		/*!< in/out: block which is modified */
	lsn_t		lsn)		/*!< in: oldest modification */
{
	ut_ad(!buf_pool_mutex_own(buf_pool));
	ut_ad(log_flush_order_mutex_own());
	ut_ad(buf_page_mutex_own(block));

	buf_flush_list_mutex_enter(buf_pool);

	ut_ad((UT_LIST_GET_FIRST(buf_pool->flush_list) == NULL)
	      || (UT_LIST_GET_FIRST(buf_pool->flush_list)->oldest_modification
		  <= lsn));

	/* If we are in the recovery then we need to update the flush
	red-black tree as well. */
	if (buf_pool->flush_rbt != NULL) {
		buf_flush_list_mutex_exit(buf_pool);
		buf_flush_insert_sorted_into_flush_list(buf_pool, block, lsn);
		return;
	}

	ut_ad(buf_block_get_state(block) == BUF_BLOCK_FILE_PAGE);
	ut_ad(!block->page.in_flush_list);

	ut_d(block->page.in_flush_list = TRUE);
	block->page.oldest_modification = lsn;

	UT_LIST_ADD_FIRST(buf_pool->flush_list, &block->page);

	incr_flush_list_size_in_bytes(block, buf_pool);

#ifdef UNIV_DEBUG_VALGRIND
	void*	p;

	if (block->page.size.is_compressed()) {
		p = block->page.zip.data;
	} else {
		p = block->frame;
	}

	UNIV_MEM_ASSERT_RW(p, block->page.size.physical());
#endif /* UNIV_DEBUG_VALGRIND */

#if defined UNIV_DEBUG || defined UNIV_BUF_DEBUG
	ut_a(buf_flush_validate_skip(buf_pool));
#endif /* UNIV_DEBUG || UNIV_BUF_DEBUG */

	buf_flush_list_mutex_exit(buf_pool);
}

/********************************************************************//**
Inserts a modified block into the flush list in the right sorted position.
This function is used by recovery, because there the modifications do not
necessarily come in the order of lsn's. */
void
buf_flush_insert_sorted_into_flush_list(
/*====================================*/
	buf_pool_t*	buf_pool,	/*!< in: buffer pool instance */
	buf_block_t*	block,		/*!< in/out: block which is modified */
	lsn_t		lsn)		/*!< in: oldest modification */
{
	buf_page_t*	prev_b;
	buf_page_t*	b;

	ut_ad(!buf_pool_mutex_own(buf_pool));
	ut_ad(log_flush_order_mutex_own());
	ut_ad(buf_page_mutex_own(block));
	ut_ad(buf_block_get_state(block) == BUF_BLOCK_FILE_PAGE);

	buf_flush_list_mutex_enter(buf_pool);

	/* The field in_LRU_list is protected by buf_pool->mutex, which
	we are not holding.  However, while a block is in the flush
	list, it is dirty and cannot be discarded, not from the
	page_hash or from the LRU list.  At most, the uncompressed
	page frame of a compressed block may be discarded or created
	(copying the block->page to or from a buf_page_t that is
	dynamically allocated from buf_buddy_alloc()).  Because those
	transitions hold block->mutex and the flush list mutex (via
	buf_flush_relocate_on_flush_list()), there is no possibility
	of a race condition in the assertions below. */
	ut_ad(block->page.in_LRU_list);
	ut_ad(block->page.in_page_hash);
	/* buf_buddy_block_register() will take a block in the
	BUF_BLOCK_MEMORY state, not a file page. */
	ut_ad(!block->page.in_zip_hash);

	ut_ad(!block->page.in_flush_list);
	ut_d(block->page.in_flush_list = TRUE);
	block->page.oldest_modification = lsn;

#ifdef UNIV_DEBUG_VALGRIND
	void*	p;

	if (block->page.size.is_compressed()) {
		p = block->page.zip.data;
	} else {
		p = block->frame;
	}

	UNIV_MEM_ASSERT_RW(p, block->page.size.physical());
#endif /* UNIV_DEBUG_VALGRIND */

	prev_b = NULL;

	/* For the most part when this function is called the flush_rbt
	should not be NULL. In a very rare boundary case it is possible
	that the flush_rbt has already been freed by the recovery thread
	before the last page was hooked up in the flush_list by the
	io-handler thread. In that case we'll just do a simple
	linear search in the else block. */
	if (buf_pool->flush_rbt != NULL) {

		prev_b = buf_flush_insert_in_flush_rbt(&block->page);

	} else {

		b = UT_LIST_GET_FIRST(buf_pool->flush_list);

		while (b != NULL && b->oldest_modification
		       > block->page.oldest_modification) {

			ut_ad(b->in_flush_list);
			prev_b = b;
			b = UT_LIST_GET_NEXT(list, b);
		}
	}

	if (prev_b == NULL) {
		UT_LIST_ADD_FIRST(buf_pool->flush_list, &block->page);
	} else {
		UT_LIST_INSERT_AFTER(buf_pool->flush_list, prev_b, &block->page);
	}

	incr_flush_list_size_in_bytes(block, buf_pool);

#if defined UNIV_DEBUG || defined UNIV_BUF_DEBUG
	ut_a(buf_flush_validate_low(buf_pool));
#endif /* UNIV_DEBUG || UNIV_BUF_DEBUG */

	buf_flush_list_mutex_exit(buf_pool);
}

/********************************************************************//**
Returns TRUE if the file page block is immediately suitable for replacement,
i.e., the transition FILE_PAGE => NOT_USED allowed.
@return TRUE if can replace immediately */
ibool
buf_flush_ready_for_replace(
/*========================*/
	buf_page_t*	bpage)	/*!< in: buffer control block, must be
				buf_page_in_file(bpage) and in the LRU list */
{
#ifdef UNIV_DEBUG
	buf_pool_t*	buf_pool = buf_pool_from_bpage(bpage);
	ut_ad(buf_pool_mutex_own(buf_pool));
#endif /* UNIV_DEBUG */
	ut_ad(mutex_own(buf_page_get_mutex(bpage)));
	ut_ad(bpage->in_LRU_list);

	if (buf_page_in_file(bpage)) {

		return(bpage->oldest_modification == 0		/* Block 没有被修改 */
		       && bpage->buf_fix_count == 0			/* 没有线程正在读该 Page */
		       && buf_page_get_io_fix(bpage) == BUF_IO_NONE);	/* 表示该页目前没有任何 IO 操作 */
	}

	ib::fatal() << "Buffer block " << bpage << " state " <<  bpage->state
		<< " in the LRU list!";

	return(FALSE);
}

/********************************************************************//**
Returns true if the block is modified and ready for flushing.
@return true if can flush immediately */
bool
buf_flush_ready_for_flush(
/*======================*/
	buf_page_t*	bpage,	/*!< in: buffer control block, must be
				buf_page_in_file(bpage) */
	buf_flush_t	flush_type)/*!< in: type of flush */
{
#ifdef UNIV_DEBUG
	buf_pool_t*	buf_pool = buf_pool_from_bpage(bpage);
	ut_ad(buf_pool_mutex_own(buf_pool));
#endif /* UNIV_DEBUG */

	ut_a(buf_page_in_file(bpage));
	ut_ad(mutex_own(buf_page_get_mutex(bpage)));
	ut_ad(flush_type < BUF_FLUSH_N_TYPES);

	if (bpage->oldest_modification == 0
	    || buf_page_get_io_fix(bpage) != BUF_IO_NONE) {
		return(false);
	}

	ut_ad(bpage->in_flush_list);

	switch (flush_type) {
	case BUF_FLUSH_LIST:
	case BUF_FLUSH_LRU:
	case BUF_FLUSH_SINGLE_PAGE:
		return(true);

	case BUF_FLUSH_N_TYPES:
		break;
	}

	ut_error;
	return(false);
}

/********************************************************************//**
Remove a block from the flush list of modified blocks. */
void
buf_flush_remove(
/*=============*/
	buf_page_t*	bpage)	/*!< in: pointer to the block in question */
{
	buf_pool_t*	buf_pool = buf_pool_from_bpage(bpage);

	ut_ad(buf_pool_mutex_own(buf_pool));
	ut_ad(mutex_own(buf_page_get_mutex(bpage)));
	ut_ad(bpage->in_flush_list);

	buf_flush_list_mutex_enter(buf_pool);

	/* Important that we adjust the hazard pointer before removing
	the bpage from flush list. */
	buf_pool->flush_hp.adjust(bpage);

	switch (buf_page_get_state(bpage)) {
	case BUF_BLOCK_POOL_WATCH:
	case BUF_BLOCK_ZIP_PAGE:
		/* Clean compressed pages should not be on the flush list */
	case BUF_BLOCK_NOT_USED:
	case BUF_BLOCK_READY_FOR_USE:
	case BUF_BLOCK_MEMORY:
	case BUF_BLOCK_REMOVE_HASH:
		ut_error;
		return;
	case BUF_BLOCK_ZIP_DIRTY:
		buf_page_set_state(bpage, BUF_BLOCK_ZIP_PAGE);
		UT_LIST_REMOVE(buf_pool->flush_list, bpage);
#if defined UNIV_DEBUG || defined UNIV_BUF_DEBUG
		buf_LRU_insert_zip_clean(bpage);
#endif /* UNIV_DEBUG || UNIV_BUF_DEBUG */
		break;
	case BUF_BLOCK_FILE_PAGE:
		UT_LIST_REMOVE(buf_pool->flush_list, bpage);
		break;
	}

	/* If the flush_rbt is active then delete from there as well. */
	if (buf_pool->flush_rbt != NULL) {
		buf_flush_delete_from_flush_rbt(bpage);
	}

	/* Must be done after we have removed it from the flush_rbt
	because we assert on in_flush_list in comparison function. */
	ut_d(bpage->in_flush_list = FALSE);

	buf_pool->stat.flush_list_bytes -= bpage->size.physical();

	bpage->oldest_modification = 0;

#if defined UNIV_DEBUG || defined UNIV_BUF_DEBUG
	ut_a(buf_flush_validate_skip(buf_pool));
#endif /* UNIV_DEBUG || UNIV_BUF_DEBUG */

	/* If there is an observer that want to know if the asynchronous
	flushing was done then notify it. */
	if (bpage->flush_observer != NULL) {
		bpage->flush_observer->notify_remove(buf_pool, bpage);

		bpage->flush_observer = NULL;
	}

	buf_flush_list_mutex_exit(buf_pool);
}

/*******************************************************************//**
Relocates a buffer control block on the flush_list.
Note that it is assumed that the contents of bpage have already been
copied to dpage.
IMPORTANT: When this function is called bpage and dpage are not
exact copies of each other. For example, they both will have different
::state. Also the ::list pointers in dpage may be stale. We need to
use the current list node (bpage) to do the list manipulation because
the list pointers could have changed between the time that we copied
the contents of bpage to the dpage and the flush list manipulation
below. */
void
buf_flush_relocate_on_flush_list(
/*=============================*/
	buf_page_t*	bpage,	/*!< in/out: control block being moved */
	buf_page_t*	dpage)	/*!< in/out: destination block */
{
	buf_page_t*	prev;
	buf_page_t*	prev_b = NULL;
	buf_pool_t*	buf_pool = buf_pool_from_bpage(bpage);

	ut_ad(buf_pool_mutex_own(buf_pool));
	/* Must reside in the same buffer pool. */
	ut_ad(buf_pool == buf_pool_from_bpage(dpage));

	ut_ad(mutex_own(buf_page_get_mutex(bpage)));

	buf_flush_list_mutex_enter(buf_pool);

	/* FIXME: At this point we have both buf_pool and flush_list
	mutexes. Theoretically removal of a block from flush list is
	only covered by flush_list mutex but currently we do
	have buf_pool mutex in buf_flush_remove() therefore this block
	is guaranteed to be in the flush list. We need to check if
	this will work without the assumption of block removing code
	having the buf_pool mutex. */
	ut_ad(bpage->in_flush_list);
	ut_ad(dpage->in_flush_list);

	/* If recovery is active we must swap the control blocks in
	the flush_rbt as well. */
	if (buf_pool->flush_rbt != NULL) {
		buf_flush_delete_from_flush_rbt(bpage);
		prev_b = buf_flush_insert_in_flush_rbt(dpage);
	}

	/* Important that we adjust the hazard pointer before removing
	the bpage from the flush list. */
	buf_pool->flush_hp.adjust(bpage);

	/* Must be done after we have removed it from the flush_rbt
	because we assert on in_flush_list in comparison function. */
	ut_d(bpage->in_flush_list = FALSE);

	prev = UT_LIST_GET_PREV(list, bpage);
	UT_LIST_REMOVE(buf_pool->flush_list, bpage);

	if (prev) {
		ut_ad(prev->in_flush_list);
		UT_LIST_INSERT_AFTER( buf_pool->flush_list, prev, dpage);
	} else {
		UT_LIST_ADD_FIRST(buf_pool->flush_list, dpage);
	}

	/* Just an extra check. Previous in flush_list
	should be the same control block as in flush_rbt. */
	ut_a(buf_pool->flush_rbt == NULL || prev_b == prev);

#if defined UNIV_DEBUG || defined UNIV_BUF_DEBUG
	ut_a(buf_flush_validate_low(buf_pool));
#endif /* UNIV_DEBUG || UNIV_BUF_DEBUG */

	buf_flush_list_mutex_exit(buf_pool);
}

/********************************************************************//**
Updates the flush system data structures when a write is completed. */
void
buf_flush_write_complete(
/*=====================*/
	buf_page_t*	bpage)	/*!< in: pointer to the block in question */
{
	buf_flush_t	flush_type;
	buf_pool_t*	buf_pool = buf_pool_from_bpage(bpage);

	ut_ad(bpage);

	buf_flush_remove(bpage);

	flush_type = buf_page_get_flush_type(bpage);
	buf_pool->n_flush[flush_type]--;

	if (buf_pool->n_flush[flush_type] == 0
	    && buf_pool->init_flush[flush_type] == FALSE) {

		/* The running flush batch has ended */

		os_event_set(buf_pool->no_flush[flush_type]);
	}

	buf_dblwr_update(bpage, flush_type);
}
#endif /* !UNIV_HOTBACKUP */

/** Calculate the checksum of a page from compressed table and update
the page.
@param[in,out]	page	page to update
@param[in]	size	compressed page size
@param[in]	lsn	LSN to stamp on the page */
void
buf_flush_update_zip_checksum(
	buf_frame_t*	page,
	ulint		size,
	lsn_t		lsn)
{
	ut_a(size > 0);

	const uint32_t	checksum = page_zip_calc_checksum(
		page, size,
		static_cast<srv_checksum_algorithm_t>(srv_checksum_algorithm));

	mach_write_to_8(page + FIL_PAGE_LSN, lsn);
	mach_write_to_4(page + FIL_PAGE_SPACE_OR_CHKSUM, checksum);
}

/** Initialize a page for writing to the tablespace.
@param[in]	block		buffer block; NULL if bypassing the buffer pool
@param[in,out]	page		page frame
@param[in,out]	page_zip_	compressed page, or NULL if uncompressed
@param[in]	newest_lsn	newest modification LSN to the page
@param[in]	skip_checksum	whether to disable the page checksum */
void
buf_flush_init_for_writing(
	const buf_block_t*	block,
	byte*			page,
	void*			page_zip_,
	lsn_t			newest_lsn,
	bool			skip_checksum)
{
	ib_uint32_t	checksum = BUF_NO_CHECKSUM_MAGIC;

	ut_ad(block == NULL || block->frame == page);
	ut_ad(block == NULL || page_zip_ == NULL
	      || &block->page.zip == page_zip_);
	ut_ad(page);

	if (page_zip_) {
		page_zip_des_t*	page_zip;
		ulint		size;

		page_zip = static_cast<page_zip_des_t*>(page_zip_);
		size = page_zip_get_size(page_zip);

		ut_ad(size);
		ut_ad(ut_is_2pow(size));
		ut_ad(size <= UNIV_ZIP_SIZE_MAX);

		switch (fil_page_get_type(page)) {
		case FIL_PAGE_TYPE_ALLOCATED:
		case FIL_PAGE_INODE:
		case FIL_PAGE_IBUF_BITMAP:
		case FIL_PAGE_TYPE_FSP_HDR:
		case FIL_PAGE_TYPE_XDES:
			/* These are essentially uncompressed pages. */
			memcpy(page_zip->data, page, size);
			/* fall through */
		case FIL_PAGE_TYPE_ZBLOB:
		case FIL_PAGE_TYPE_ZBLOB2:
		case FIL_PAGE_INDEX:
		case FIL_PAGE_RTREE:

			buf_flush_update_zip_checksum(
				page_zip->data, size, newest_lsn);

			return;
		}

		ib::error() << "The compressed page to be written"
			" seems corrupt:";
		ut_print_buf(stderr, page, size);
		fputs("\nInnoDB: Possibly older version of the page:", stderr);
		ut_print_buf(stderr, page_zip->data, size);
		putc('\n', stderr);
		ut_error;
	}

	/* Write the newest modification lsn to the page header and trailer */
	mach_write_to_8(page + FIL_PAGE_LSN, newest_lsn);

	mach_write_to_8(page + UNIV_PAGE_SIZE - FIL_PAGE_END_LSN_OLD_CHKSUM,
			newest_lsn);

	if (skip_checksum) {
		mach_write_to_4(page + FIL_PAGE_SPACE_OR_CHKSUM, checksum);
	} else {
		if (block != NULL && UNIV_PAGE_SIZE == 16384) {
			/* The page type could be garbage in old files
			created before MySQL 5.5. Such files always
			had a page size of 16 kilobytes. */
			ulint	page_type = fil_page_get_type(page);
			ulint	reset_type = page_type;

			switch (block->page.id.page_no() % 16384) {
			case 0:
				reset_type = block->page.id.page_no() == 0
					? FIL_PAGE_TYPE_FSP_HDR
					: FIL_PAGE_TYPE_XDES;
				break;
			case 1:
				reset_type = FIL_PAGE_IBUF_BITMAP;
				break;
			default:
				switch (page_type) {
				case FIL_PAGE_INDEX:
				case FIL_PAGE_RTREE:
				case FIL_PAGE_UNDO_LOG:
				case FIL_PAGE_INODE:
				case FIL_PAGE_IBUF_FREE_LIST:
				case FIL_PAGE_TYPE_ALLOCATED:
				case FIL_PAGE_TYPE_SYS:
				case FIL_PAGE_TYPE_TRX_SYS:
				case FIL_PAGE_TYPE_BLOB:
				case FIL_PAGE_TYPE_ZBLOB:
				case FIL_PAGE_TYPE_ZBLOB2:
					break;
				case FIL_PAGE_TYPE_FSP_HDR:
				case FIL_PAGE_TYPE_XDES:
				case FIL_PAGE_IBUF_BITMAP:
					/* These pages should have
					predetermined page numbers
					(see above). */
				default:
					reset_type = FIL_PAGE_TYPE_UNKNOWN;
					break;
				}
			}

			if (UNIV_UNLIKELY(page_type != reset_type)) {
				ib::info()
					<< "Resetting invalid page "
					<< block->page.id << " type "
					<< page_type << " to "
					<< reset_type << " when flushing.";
				fil_page_set_type(page, reset_type);
			}
		}

		switch ((srv_checksum_algorithm_t) srv_checksum_algorithm) {
		case SRV_CHECKSUM_ALGORITHM_CRC32:
		case SRV_CHECKSUM_ALGORITHM_STRICT_CRC32:
			checksum = buf_calc_page_crc32(page);
			mach_write_to_4(page + FIL_PAGE_SPACE_OR_CHKSUM,
					checksum);
			break;
		case SRV_CHECKSUM_ALGORITHM_INNODB:
		case SRV_CHECKSUM_ALGORITHM_STRICT_INNODB:
			checksum = (ib_uint32_t) buf_calc_page_new_checksum(
				page);
			mach_write_to_4(page + FIL_PAGE_SPACE_OR_CHKSUM,
					checksum);
			checksum = (ib_uint32_t) buf_calc_page_old_checksum(
				page);
			break;
		case SRV_CHECKSUM_ALGORITHM_NONE:
		case SRV_CHECKSUM_ALGORITHM_STRICT_NONE:
			mach_write_to_4(page + FIL_PAGE_SPACE_OR_CHKSUM,
					checksum);
			break;
			/* no default so the compiler will emit a warning if
			new enum is added and not handled here */
		}
	}

	/* With the InnoDB checksum, we overwrite the first 4 bytes of
	the end lsn field to store the old formula checksum. Since it
	depends also on the field FIL_PAGE_SPACE_OR_CHKSUM, it has to
	be calculated after storing the new formula checksum.

	In other cases we write the same value to both fields.
	If CRC32 is used then it is faster to use that checksum
	(calculated above) instead of calculating another one.
	We can afford to store something other than
	buf_calc_page_old_checksum() or BUF_NO_CHECKSUM_MAGIC in
	this field because the file will not be readable by old
	versions of MySQL/InnoDB anyway (older than MySQL 5.6.3) */

	mach_write_to_4(page + UNIV_PAGE_SIZE - FIL_PAGE_END_LSN_OLD_CHKSUM,
			checksum);
}

#ifndef UNIV_HOTBACKUP
/********************************************************************//**
Does an asynchronous write of a buffer page. NOTE: in simulated aio and
also when the doublewrite buffer is used, we must call
buf_dblwr_flush_buffered_writes after we have posted a batch of
writes! */
static
void
buf_flush_write_block_low(
/*======================*/
	buf_page_t*	bpage,		/*!< in: buffer block to write */
	buf_flush_t	flush_type,	/*!< in: type of flush */
	bool		sync)		/*!< in: true if sync IO request */
{
	page_t*	frame = NULL;

#ifdef UNIV_DEBUG
	buf_pool_t*	buf_pool = buf_pool_from_bpage(bpage);
	ut_ad(!buf_pool_mutex_own(buf_pool));
#endif /* UNIV_DEBUG */

	DBUG_PRINT("ib_buf", ("flush %s %u page " UINT32PF ":" UINT32PF,
			      sync ? "sync" : "async", (unsigned) flush_type,
			      bpage->id.space(), bpage->id.page_no()));

	ut_ad(buf_page_in_file(bpage));

	/* We are not holding buf_pool->mutex or block_mutex here.
	Nevertheless, it is safe to access bpage, because it is
	io_fixed and oldest_modification != 0.  Thus, it cannot be
	relocated in the buffer pool or removed from flush_list or
	LRU_list. */
	ut_ad(!buf_pool_mutex_own(buf_pool));
	ut_ad(!buf_flush_list_mutex_own(buf_pool));
	ut_ad(!buf_page_get_mutex(bpage)->is_owned());
	ut_ad(buf_page_get_io_fix(bpage) == BUF_IO_WRITE);
	ut_ad(bpage->oldest_modification != 0);

#ifdef UNIV_IBUF_COUNT_DEBUG
	ut_a(ibuf_count_get(bpage->id) == 0);
#endif /* UNIV_IBUF_COUNT_DEBUG */

	ut_ad(bpage->newest_modification != 0);

	/* Force the log to the disk before writing the modified block */
	if (!srv_read_only_mode) {
		log_write_up_to(bpage->newest_modification, true);
	}

	switch (buf_page_get_state(bpage)) {
	case BUF_BLOCK_POOL_WATCH:
	case BUF_BLOCK_ZIP_PAGE: /* The page should be dirty. */
	case BUF_BLOCK_NOT_USED:
	case BUF_BLOCK_READY_FOR_USE:
	case BUF_BLOCK_MEMORY:
	case BUF_BLOCK_REMOVE_HASH:
		ut_error;
		break;
	case BUF_BLOCK_ZIP_DIRTY:
		frame = bpage->zip.data;

		mach_write_to_8(frame + FIL_PAGE_LSN,
				bpage->newest_modification);

		ut_a(page_zip_verify_checksum(frame, bpage->size.physical()));
		break;
	case BUF_BLOCK_FILE_PAGE:
		frame = bpage->zip.data;
		if (!frame) {
			frame = ((buf_block_t*) bpage)->frame;
		}

		buf_flush_init_for_writing(
			reinterpret_cast<const buf_block_t*>(bpage),
			reinterpret_cast<const buf_block_t*>(bpage)->frame,
			bpage->zip.data ? &bpage->zip : NULL,
			bpage->newest_modification,
			fsp_is_checksum_disabled(bpage->id.space()));
		break;
	}

	/* Disable use of double-write buffer for temporary tablespace.
	Given the nature and load of temporary tablespace doublewrite buffer
	adds an overhead during flushing. */

	if (!srv_use_doublewrite_buf
	    || buf_dblwr == NULL
	    || srv_read_only_mode
	    || fsp_is_system_temporary(bpage->id.space())) {

		ut_ad(!srv_read_only_mode
		      || fsp_is_system_temporary(bpage->id.space()));

		ulint	type = IORequest::WRITE | IORequest::DO_NOT_WAKE;

		IORequest	request(type);

		fil_io(request,
		       sync, bpage->id, bpage->size, 0, bpage->size.physical(),
		       frame, bpage);

	} else if (flush_type == BUF_FLUSH_SINGLE_PAGE) {
		buf_dblwr_write_single_page(bpage, sync);
	} else {
		ut_ad(!sync);
		buf_dblwr_add_to_batch(bpage);
	}

	/* When doing single page flushing the IO is done synchronously
	and we flush the changes to disk only for the tablespace we
	are working on. */
	if (sync) {
		ut_ad(flush_type == BUF_FLUSH_SINGLE_PAGE);
		fil_flush(bpage->id.space());

		/* true means we want to evict this page from the
		LRU list as well. */
		buf_page_io_complete(bpage, true);
	}

	/* Increment the counter of I/O operations used
	for selecting LRU policy. */
	buf_LRU_stat_inc_io();
}

/********************************************************************//**
Writes a flushable page asynchronously from the buffer pool to a file.
NOTE: in simulated aio we must call
os_aio_simulated_wake_handler_threads after we have posted a batch of
writes! NOTE: buf_pool->mutex and buf_page_get_mutex(bpage) must be
held upon entering this function, and they will be released by this
function if it returns true.
@return TRUE if the page was flushed */
ibool
buf_flush_page(
/*===========*/
	buf_pool_t*	buf_pool,	/*!< in: buffer pool instance */
	buf_page_t*	bpage,		/*!< in: buffer control block */
	buf_flush_t	flush_type,	/*!< in: type of flush */
	bool		sync)		/*!< in: true if sync IO request */
{
	BPageMutex*	block_mutex;

	ut_ad(flush_type < BUF_FLUSH_N_TYPES);
	ut_ad(buf_pool_mutex_own(buf_pool));
	ut_ad(buf_page_in_file(bpage));
	ut_ad(!sync || flush_type == BUF_FLUSH_SINGLE_PAGE);

	block_mutex = buf_page_get_mutex(bpage);
	ut_ad(mutex_own(block_mutex));

	ut_ad(buf_flush_ready_for_flush(bpage, flush_type));

	bool	is_uncompressed;

	is_uncompressed = (buf_page_get_state(bpage) == BUF_BLOCK_FILE_PAGE);
	ut_ad(is_uncompressed == (block_mutex != &buf_pool->zip_mutex));

	ibool		flush;
	rw_lock_t*	rw_lock;
	bool		no_fix_count = bpage->buf_fix_count == 0;

	if (!is_uncompressed) {
		flush = TRUE;
		rw_lock = NULL;
	} else if (!(no_fix_count || flush_type == BUF_FLUSH_LIST)
		   || (!no_fix_count
		       && srv_shutdown_state <= SRV_SHUTDOWN_CLEANUP
		       && fsp_is_system_temporary(bpage->id.space()))) {
		/* This is a heuristic, to avoid expensive SX attempts. */
		/* For table residing in temporary tablespace sync is done
		using IO_FIX and so before scheduling for flush ensure that
		page is not fixed. */
		flush = FALSE;
	} else {
		rw_lock = &reinterpret_cast<buf_block_t*>(bpage)->lock;
		if (flush_type != BUF_FLUSH_LIST) {
			flush = rw_lock_sx_lock_nowait(rw_lock, BUF_IO_WRITE);
		} else {
			/* Will SX lock later */
			flush = TRUE;
		}
	}

	if (flush) {

		/* We are committed to flushing by the time we get here */

		buf_page_set_io_fix(bpage, BUF_IO_WRITE);

		buf_page_set_flush_type(bpage, flush_type);

		if (buf_pool->n_flush[flush_type] == 0) {
			os_event_reset(buf_pool->no_flush[flush_type]);
		}

		++buf_pool->n_flush[flush_type];

		mutex_exit(block_mutex);

		buf_pool_mutex_exit(buf_pool);

		if (flush_type == BUF_FLUSH_LIST
		    && is_uncompressed
		    && !rw_lock_sx_lock_nowait(rw_lock, BUF_IO_WRITE)) {

			if (!fsp_is_system_temporary(bpage->id.space())) {
				/* avoiding deadlock possibility involves
				doublewrite buffer, should flush it, because
				it might hold the another block->lock. */
				buf_dblwr_flush_buffered_writes();
			} else {
				buf_dblwr_sync_datafiles();
			}

			rw_lock_sx_lock_gen(rw_lock, BUF_IO_WRITE);
		}

		/* If there is an observer that want to know if the asynchronous
		flushing was sent then notify it.
		Note: we set flush observer to a page with x-latch, so we can
		guarantee that notify_flush and notify_remove are called in pair
		with s-latch on a uncompressed page. */
		if (bpage->flush_observer != NULL) {
			buf_pool_mutex_enter(buf_pool);

			bpage->flush_observer->notify_flush(buf_pool, bpage);

			buf_pool_mutex_exit(buf_pool);
		}

		/* Even though bpage is not protected by any mutex at this
		point, it is safe to access bpage, because it is io_fixed and
		oldest_modification != 0.  Thus, it cannot be relocated in the
		buffer pool or removed from flush_list or LRU_list. */

		buf_flush_write_block_low(bpage, flush_type, sync);
	}

	return(flush);
}

# if defined UNIV_DEBUG || defined UNIV_IBUF_DEBUG
/********************************************************************//**
Writes a flushable page asynchronously from the buffer pool to a file.
NOTE: buf_pool->mutex and block->mutex must be held upon entering this
function, and they will be released by this function after flushing.
This is loosely based on buf_flush_batch() and buf_flush_page().
@return TRUE if the page was flushed and the mutexes released */
ibool
buf_flush_page_try(
/*===============*/
	buf_pool_t*	buf_pool,	/*!< in/out: buffer pool instance */
	buf_block_t*	block)		/*!< in/out: buffer control block */
{
	ut_ad(buf_pool_mutex_own(buf_pool));
	ut_ad(buf_block_get_state(block) == BUF_BLOCK_FILE_PAGE);
	ut_ad(buf_page_mutex_own(block));

	if (!buf_flush_ready_for_flush(&block->page, BUF_FLUSH_SINGLE_PAGE)) {
		return(FALSE);
	}

	/* The following call will release the buffer pool and
	block mutex. */
	return(buf_flush_page(
			buf_pool, &block->page,
			BUF_FLUSH_SINGLE_PAGE, true));
}
# endif /* UNIV_DEBUG || UNIV_IBUF_DEBUG */

/** Check the page is in buffer pool and can be flushed.
@param[in]	page_id		page id
@param[in]	flush_type	BUF_FLUSH_LRU or BUF_FLUSH_LIST
@return true if the page can be flushed. */
static
bool
buf_flush_check_neighbor(
	const page_id_t&	page_id,
	buf_flush_t		flush_type)
{
	buf_page_t*	bpage;
	buf_pool_t*	buf_pool = buf_pool_get(page_id);
	bool		ret;

	ut_ad(flush_type == BUF_FLUSH_LRU
	      || flush_type == BUF_FLUSH_LIST);

	buf_pool_mutex_enter(buf_pool);

	/* We only want to flush pages from this buffer pool. */
	bpage = buf_page_hash_get(buf_pool, page_id);

	if (!bpage) {

		buf_pool_mutex_exit(buf_pool);
		return(false);
	}

	ut_a(buf_page_in_file(bpage));

	/* We avoid flushing 'non-old' blocks in an LRU flush,
	because the flushed blocks are soon freed */

	ret = false;
	if (flush_type != BUF_FLUSH_LRU || buf_page_is_old(bpage)) {
		BPageMutex* block_mutex = buf_page_get_mutex(bpage);

		mutex_enter(block_mutex);
		if (buf_flush_ready_for_flush(bpage, flush_type)) {
			ret = true;
		}
		mutex_exit(block_mutex);
	}
	buf_pool_mutex_exit(buf_pool);

	return(ret);
}

/** Flushes to disk all flushable pages within the flush area.
@param[in]	page_id		page id
@param[in]	flush_type	BUF_FLUSH_LRU or BUF_FLUSH_LIST
@param[in]	n_flushed	number of pages flushed so far in this batch
@param[in]	n_to_flush	maximum number of pages we are allowed to flush
@return number of pages flushed */
static
ulint
buf_flush_try_neighbors(
	const page_id_t&	page_id,
	buf_flush_t		flush_type,
	ulint			n_flushed,
	ulint			n_to_flush)
{
	ulint		i;
	ulint		low;
	ulint		high;
	ulint		count = 0;
	buf_pool_t*	buf_pool = buf_pool_get(page_id);

	ut_ad(flush_type == BUF_FLUSH_LRU || flush_type == BUF_FLUSH_LIST);

	if (UT_LIST_GET_LEN(buf_pool->LRU) < BUF_LRU_OLD_MIN_LEN
	    || srv_flush_neighbors == 0) {
		/* If there is little space or neighbor flushing is
		not enabled then just flush the victim. */
		low = page_id.page_no();
		high = page_id.page_no() + 1;
	} else {
		/* When flushed, dirty blocks are searched in
		neighborhoods of this size, and flushed along with the
		original page. */

		ulint	buf_flush_area;

		buf_flush_area	= ut_min(
			BUF_READ_AHEAD_AREA(buf_pool),
			buf_pool->curr_size / 16);

		low = (page_id.page_no() / buf_flush_area) * buf_flush_area;
		high = (page_id.page_no() / buf_flush_area + 1) * buf_flush_area;

		if (srv_flush_neighbors == 1) {
			/* adjust 'low' and 'high' to limit
			   for contiguous dirty area */
			if (page_id.page_no() > low) {
				for (i = page_id.page_no() - 1; i >= low; i--) {
					if (!buf_flush_check_neighbor(
						page_id_t(page_id.space(), i),
						flush_type)) {

						break;
					}

					if (i == low) {
						/* Avoid overwrap when low == 0
						and calling
						buf_flush_check_neighbor() with
						i == (ulint) -1 */
						i--;
						break;
					}
				}
				low = i + 1;
			}

			for (i = page_id.page_no() + 1;
			     i < high
			     && buf_flush_check_neighbor(
				     page_id_t(page_id.space(), i),
				     flush_type);
			     i++) {
				/* do nothing */
			}
			high = i;
		}
	}

	const ulint	space_size = fil_space_get_size(page_id.space());
	if (high > space_size) {
		high = space_size;
	}

	DBUG_PRINT("ib_buf", ("flush " UINT32PF ":%u..%u",
			      page_id.space(),
			      (unsigned) low, (unsigned) high));

	for (ulint i = low; i < high; i++) {
		buf_page_t*	bpage;

		if ((count + n_flushed) >= n_to_flush) {

			/* We have already flushed enough pages and
			should call it a day. There is, however, one
			exception. If the page whose neighbors we
			are flushing has not been flushed yet then
			we'll try to flush the victim that we
			selected originally. */
			if (i <= page_id.page_no()) {
				i = page_id.page_no();
			} else {
				break;
			}
		}

		const page_id_t	cur_page_id(page_id.space(), i);

		buf_pool = buf_pool_get(cur_page_id);

		buf_pool_mutex_enter(buf_pool);

		/* We only want to flush pages from this buffer pool. */
		bpage = buf_page_hash_get(buf_pool, cur_page_id);

		if (bpage == NULL) {

			buf_pool_mutex_exit(buf_pool);
			continue;
		}

		ut_a(buf_page_in_file(bpage));

		/* We avoid flushing 'non-old' blocks in an LRU flush,
		because the flushed blocks are soon freed */

		if (flush_type != BUF_FLUSH_LRU
		    || i == page_id.page_no()
		    || buf_page_is_old(bpage)) {

			BPageMutex* block_mutex = buf_page_get_mutex(bpage);

			mutex_enter(block_mutex);

			if (buf_flush_ready_for_flush(bpage, flush_type)
			    && (i == page_id.page_no()
				|| bpage->buf_fix_count == 0)) {

				/* We also try to flush those
				neighbors != offset */

				if (buf_flush_page(
					buf_pool, bpage, flush_type, false)) {

					++count;
				} else {
					mutex_exit(block_mutex);
					buf_pool_mutex_exit(buf_pool);
				}

				continue;
			} else {
				mutex_exit(block_mutex);
			}
		}
		buf_pool_mutex_exit(buf_pool);
	}

	if (count > 1) {
		MONITOR_INC_VALUE_CUMULATIVE(
			MONITOR_FLUSH_NEIGHBOR_TOTAL_PAGE,
			MONITOR_FLUSH_NEIGHBOR_COUNT,
			MONITOR_FLUSH_NEIGHBOR_PAGES,
			(count - 1));
	}

	return(count);
}

/** Check if the block is modified and ready for flushing.
If the the block is ready to flush then flush the page and try o flush
its neighbors.
@param[in]	bpage		buffer control block,
must be buf_page_in_file(bpage)
@param[in]	flush_type	BUF_FLUSH_LRU or BUF_FLUSH_LIST
@param[in]	n_to_flush	number of pages to flush
@param[in,out]	count		number of pages flushed
@return TRUE if buf_pool mutex was released during this function.
This does not guarantee that some pages were written as well.
Number of pages written are incremented to the count. */
static
bool
buf_flush_page_and_try_neighbors(
	buf_page_t*		bpage,
	buf_flush_t		flush_type,
	ulint			n_to_flush,
	ulint*			count)
{
#ifdef UNIV_DEBUG
	buf_pool_t*	buf_pool = buf_pool_from_bpage(bpage);

	ut_ad(buf_pool_mutex_own(buf_pool));
#endif /* UNIV_DEBUG */

	bool		flushed;
	BPageMutex*	block_mutex = buf_page_get_mutex(bpage);

	mutex_enter(block_mutex);

	ut_a(buf_page_in_file(bpage));

	if (buf_flush_ready_for_flush(bpage, flush_type)) {
		buf_pool_t*	buf_pool;

		buf_pool = buf_pool_from_bpage(bpage);

		const page_id_t	page_id = bpage->id;

		mutex_exit(block_mutex);

		buf_pool_mutex_exit(buf_pool);

		/* Try to flush also all the neighbors */
		*count += buf_flush_try_neighbors(
			page_id, flush_type, *count, n_to_flush);

		buf_pool_mutex_enter(buf_pool);
		flushed = TRUE;
	} else {
		mutex_exit(block_mutex);

		flushed = false;
	}

	ut_ad(buf_pool_mutex_own(buf_pool));

	return(flushed);
}

/*******************************************************************//**
This utility moves the uncompressed frames of pages to the free list.
Note that this function does not actually flush any data to disk. It
just detaches the uncompressed frames from the compressed pages at the
tail of the unzip_LRU and puts those freed frames in the free list.
Note that it is a best effort attempt and it is not guaranteed that
after a call to this function there will be 'max' blocks in the free
list.
@return number of blocks moved to the free list. */
static
ulint
buf_free_from_unzip_LRU_list_batch(
/*===============================*/
	buf_pool_t*	buf_pool,	/*!< in: buffer pool instance */
	ulint		max)		/*!< in: desired number of
					blocks in the free_list */
{
	ulint		scanned = 0;
	ulint		count = 0;
	ulint		free_len = UT_LIST_GET_LEN(buf_pool->free);
	ulint		lru_len = UT_LIST_GET_LEN(buf_pool->unzip_LRU);

	ut_ad(buf_pool_mutex_own(buf_pool));

	buf_block_t*	block = UT_LIST_GET_LAST(buf_pool->unzip_LRU);

	while (block != NULL
	       && count < max
	       && free_len < srv_LRU_scan_depth
	       && lru_len > UT_LIST_GET_LEN(buf_pool->LRU) / 10) {

		++scanned;
		if (buf_LRU_free_page(&block->page, false)) {
			/* Block was freed. buf_pool->mutex potentially
			released and reacquired */
			++count;
			block = UT_LIST_GET_LAST(buf_pool->unzip_LRU);

		} else {

			block = UT_LIST_GET_PREV(unzip_LRU, block);
		}

		free_len = UT_LIST_GET_LEN(buf_pool->free);
		lru_len = UT_LIST_GET_LEN(buf_pool->unzip_LRU);
	}

	ut_ad(buf_pool_mutex_own(buf_pool));

	if (scanned) {
		MONITOR_INC_VALUE_CUMULATIVE(
			MONITOR_LRU_BATCH_SCANNED,
			MONITOR_LRU_BATCH_SCANNED_NUM_CALL,
			MONITOR_LRU_BATCH_SCANNED_PER_CALL,
			scanned);
	}

	return(count);
}

/*******************************************************************//**
This utility flushes dirty blocks from the end of the LRU list.
The calling thread is not allowed to own any latches on pages!
It attempts to make 'max' blocks available in the free list. Note that
it is a best effort attempt and it is not guaranteed that after a call
to this function there will be 'max' blocks in the free list.
@return number of blocks for which the write request was queued. */
static
ulint
buf_flush_LRU_list_batch(
/*=====================*/
	buf_pool_t*	buf_pool,	/*!< in: buffer pool instance */
	ulint		max)		/*!< in: desired number of
					blocks in the free_list */
{
	buf_page_t*	bpage;
	ulint		scanned = 0;
	ulint		evict_count = 0;
	ulint		count = 0;
	ulint		free_len = UT_LIST_GET_LEN(buf_pool->free);
	ulint		lru_len = UT_LIST_GET_LEN(buf_pool->LRU);
	ulint		withdraw_depth = 0;

	ut_ad(buf_pool_mutex_own(buf_pool));

	if (buf_pool->curr_size < buf_pool->old_size
	    && buf_pool->withdraw_target > 0) {
		withdraw_depth = buf_pool->withdraw_target
				 - UT_LIST_GET_LEN(buf_pool->withdraw);
	}

	for (bpage = UT_LIST_GET_LAST(buf_pool->LRU);
	     bpage != NULL && count + evict_count < max
	     && free_len < srv_LRU_scan_depth + withdraw_depth
	     && lru_len > BUF_LRU_MIN_LEN;
	     ++scanned,
	     bpage = buf_pool->lru_hp.get()) {

		buf_page_t* prev = UT_LIST_GET_PREV(LRU, bpage);
		buf_pool->lru_hp.set(prev);

		BPageMutex*	block_mutex = buf_page_get_mutex(bpage);

		mutex_enter(block_mutex);

		if (buf_flush_ready_for_replace(bpage)) {
			/* block is ready for eviction i.e., it is
			clean and is not IO-fixed or buffer fixed. */
			mutex_exit(block_mutex);
			if (buf_LRU_free_page(bpage, true)) {
				++evict_count;
			}
		} else if (buf_flush_ready_for_flush(bpage, BUF_FLUSH_LRU)) {
			/* Block is ready for flush. Dispatch an IO
			request. The IO helper thread will put it on
			free list in IO completion routine. */
			mutex_exit(block_mutex);
			buf_flush_page_and_try_neighbors(
				bpage, BUF_FLUSH_LRU, max, &count);
		} else {
			/* Can't evict or dispatch this block. Go to
			previous. */
			ut_ad(buf_pool->lru_hp.is_hp(prev));
			mutex_exit(block_mutex);
		}

		ut_ad(!mutex_own(block_mutex));
		ut_ad(buf_pool_mutex_own(buf_pool));

		free_len = UT_LIST_GET_LEN(buf_pool->free);
		lru_len = UT_LIST_GET_LEN(buf_pool->LRU);
	}

	buf_pool->lru_hp.set(NULL);

	/* We keep track of all flushes happening as part of LRU
	flush. When estimating the desired rate at which flush_list
	should be flushed, we factor in this value. */
	buf_lru_flush_page_count += count;

	ut_ad(buf_pool_mutex_own(buf_pool));

	if (evict_count) {
		MONITOR_INC_VALUE_CUMULATIVE(
			MONITOR_LRU_BATCH_EVICT_TOTAL_PAGE,
			MONITOR_LRU_BATCH_EVICT_COUNT,
			MONITOR_LRU_BATCH_EVICT_PAGES,
			evict_count);
	}

	if (scanned) {
		MONITOR_INC_VALUE_CUMULATIVE(
			MONITOR_LRU_BATCH_SCANNED,
			MONITOR_LRU_BATCH_SCANNED_NUM_CALL,
			MONITOR_LRU_BATCH_SCANNED_PER_CALL,
			scanned);
	}

	return(count);
}

/*******************************************************************//**
Flush and move pages from LRU or unzip_LRU list to the free list.
Whether LRU or unzip_LRU is used depends on the state of the system.
@return number of blocks for which either the write request was queued
or in case of unzip_LRU the number of blocks actually moved to the
free list */
static
ulint
buf_do_LRU_batch(
/*=============*/
	buf_pool_t*	buf_pool,	/*!< in: buffer pool instance */
	ulint		max)		/*!< in: desired number of
					blocks in the free_list */
{
	ulint	count = 0;

	if (buf_LRU_evict_from_unzip_LRU(buf_pool)) {
		count += buf_free_from_unzip_LRU_list_batch(buf_pool, max);
	}

	if (max > count) {
		count += buf_flush_LRU_list_batch(buf_pool, max - count);
	}

	return(count);
}

/** This utility flushes dirty blocks from the end of the flush_list.
The calling thread is not allowed to own any latches on pages!
@param[in]	buf_pool	buffer pool instance
@param[in]	min_n		wished minimum mumber of blocks flushed (it is
not guaranteed that the actual number is that big, though)
@param[in]	lsn_limit	all blocks whose oldest_modification is smaller
than this should be flushed (if their number does not exceed min_n)
@return number of blocks for which the write request was queued;
ULINT_UNDEFINED if there was a flush of the same type already
running */
static
ulint
buf_do_flush_list_batch(
	buf_pool_t*		buf_pool,
	ulint			min_n,
	lsn_t			lsn_limit)
{
	ulint		count = 0;
	ulint		scanned = 0;

	ut_ad(buf_pool_mutex_own(buf_pool));

	/* Start from the end of the list looking for a suitable
	block to be flushed. */
	buf_flush_list_mutex_enter(buf_pool);
	ulint len = UT_LIST_GET_LEN(buf_pool->flush_list);

	/* In order not to degenerate this scan to O(n*n) we attempt
	to preserve pointer of previous block in the flush list. To do
	so we declare it a hazard pointer. Any thread working on the
	flush list must check the hazard pointer and if it is removing
	the same block then it must reset it. */
	for (buf_page_t* bpage = UT_LIST_GET_LAST(buf_pool->flush_list);
	     count < min_n && bpage != NULL && len > 0
	     && bpage->oldest_modification < lsn_limit;
	     bpage = buf_pool->flush_hp.get(),
	     ++scanned) {

		buf_page_t*	prev;

		ut_a(bpage->oldest_modification > 0);
		ut_ad(bpage->in_flush_list);

		prev = UT_LIST_GET_PREV(list, bpage);
		buf_pool->flush_hp.set(prev);
		buf_flush_list_mutex_exit(buf_pool);

#ifdef UNIV_DEBUG
		bool flushed =
#endif /* UNIV_DEBUG */
		buf_flush_page_and_try_neighbors(
			bpage, BUF_FLUSH_LIST, min_n, &count);

		buf_flush_list_mutex_enter(buf_pool);

		ut_ad(flushed || buf_pool->flush_hp.is_hp(prev));

		--len;
	}

	buf_pool->flush_hp.set(NULL);
	buf_flush_list_mutex_exit(buf_pool);

	if (scanned) {
		MONITOR_INC_VALUE_CUMULATIVE(
			MONITOR_FLUSH_BATCH_SCANNED,
			MONITOR_FLUSH_BATCH_SCANNED_NUM_CALL,
			MONITOR_FLUSH_BATCH_SCANNED_PER_CALL,
			scanned);
	}

	if (count) {
		MONITOR_INC_VALUE_CUMULATIVE(
			MONITOR_FLUSH_BATCH_TOTAL_PAGE,
			MONITOR_FLUSH_BATCH_COUNT,
			MONITOR_FLUSH_BATCH_PAGES,
			count);
	}

	ut_ad(buf_pool_mutex_own(buf_pool));

	return(count);
}

/** This utility flushes dirty blocks from the end of the LRU list or
flush_list.
NOTE 1: in the case of an LRU flush the calling thread may own latches to
pages: to avoid deadlocks, this function must be written so that it cannot
end up waiting for these latches! NOTE 2: in the case of a flush list flush,
the calling thread is not allowed to own any latches on pages!
@param[in]	buf_pool	buffer pool instance
@param[in]	flush_type	BUF_FLUSH_LRU or BUF_FLUSH_LIST; if
BUF_FLUSH_LIST, then the caller must not own any latches on pages
@param[in]	min_n		wished minimum mumber of blocks flushed (it is
not guaranteed that the actual number is that big, though)
@param[in]	lsn_limit	in the case of BUF_FLUSH_LIST all blocks whose
oldest_modification is smaller than this should be flushed (if their number
does not exceed min_n), otherwise ignored
@return number of blocks for which the write request was queued */
static
ulint
buf_flush_batch(
	buf_pool_t*		buf_pool,
	buf_flush_t		flush_type,
	ulint			min_n,
	lsn_t			lsn_limit)
{
	ut_ad(flush_type == BUF_FLUSH_LRU || flush_type == BUF_FLUSH_LIST);

#ifdef UNIV_DEBUG
	{
		dict_sync_check	check(true);

		ut_ad(flush_type != BUF_FLUSH_LIST
		      || !sync_check_iterate(check));
	}
#endif /* UNIV_DEBUG */

	buf_pool_mutex_enter(buf_pool);

	ulint	count = 0;

	/* Note: The buffer pool mutex is released and reacquired within
	the flush functions. */
	switch (flush_type) {
	case BUF_FLUSH_LRU:
		count = buf_do_LRU_batch(buf_pool, min_n);
		break;
	case BUF_FLUSH_LIST:
		count = buf_do_flush_list_batch(buf_pool, min_n, lsn_limit);
		break;
	default:
		ut_error;
	}

	buf_pool_mutex_exit(buf_pool);

	DBUG_PRINT("ib_buf", ("flush %u completed, %u pages",
			      unsigned(flush_type), unsigned(count)));

	return(count);
}

/******************************************************************//**
Gather the aggregated stats for both flush list and LRU list flushing.
@param page_count_flush	number of pages flushed from the end of the flush_list
@param page_count_LRU	number of pages flushed from the end of the LRU list
*/
static
void
buf_flush_stats(
/*============*/
	ulint		page_count_flush,
	ulint		page_count_LRU)
{
	DBUG_PRINT("ib_buf", ("flush completed, from flush_list %u pages, "
			      "from LRU_list %u pages",
			      unsigned(page_count_flush),
			      unsigned(page_count_LRU)));

	srv_stats.buf_pool_flushed.add(page_count_flush + page_count_LRU);
}

/******************************************************************//**
Start a buffer flush batch for LRU or flush list */
static
ibool
buf_flush_start(
/*============*/
	buf_pool_t*	buf_pool,	/*!< buffer pool instance */
	buf_flush_t	flush_type)	/*!< in: BUF_FLUSH_LRU
					or BUF_FLUSH_LIST */
{
	ut_ad(flush_type == BUF_FLUSH_LRU || flush_type == BUF_FLUSH_LIST);

	buf_pool_mutex_enter(buf_pool);

	if (buf_pool->n_flush[flush_type] > 0
	   || buf_pool->init_flush[flush_type] == TRUE) {

		/* There is already a flush batch of the same type running */

		buf_pool_mutex_exit(buf_pool);

		return(FALSE);
	}

	buf_pool->init_flush[flush_type] = TRUE;

	os_event_reset(buf_pool->no_flush[flush_type]);

	buf_pool_mutex_exit(buf_pool);

	return(TRUE);
}

/******************************************************************//**
End a buffer flush batch for LRU or flush list */
static
void
buf_flush_end(
/*==========*/
	buf_pool_t*	buf_pool,	/*!< buffer pool instance */
	buf_flush_t	flush_type)	/*!< in: BUF_FLUSH_LRU
					or BUF_FLUSH_LIST */
{
	buf_pool_mutex_enter(buf_pool);

	buf_pool->init_flush[flush_type] = FALSE;

	buf_pool->try_LRU_scan = TRUE;

	if (buf_pool->n_flush[flush_type] == 0) {

		/* The running flush batch has ended */

		os_event_set(buf_pool->no_flush[flush_type]);
	}

	buf_pool_mutex_exit(buf_pool);

	if (!srv_read_only_mode) {
		buf_dblwr_flush_buffered_writes();
	} else {
		os_aio_simulated_wake_handler_threads();
	}
}

/******************************************************************//**
Waits until a flush batch of the given type ends */
void
buf_flush_wait_batch_end(
/*=====================*/
	buf_pool_t*	buf_pool,	/*!< buffer pool instance */
	buf_flush_t	type)		/*!< in: BUF_FLUSH_LRU
					or BUF_FLUSH_LIST */
{
	ut_ad(type == BUF_FLUSH_LRU || type == BUF_FLUSH_LIST);

	if (buf_pool == NULL) {
		ulint	i;

		for (i = 0; i < srv_buf_pool_instances; ++i) {
			buf_pool_t*	buf_pool;

			buf_pool = buf_pool_from_array(i);

			thd_wait_begin(NULL, THD_WAIT_DISKIO);
			os_event_wait(buf_pool->no_flush[type]);
			thd_wait_end(NULL);
		}
	} else {
		thd_wait_begin(NULL, THD_WAIT_DISKIO);
		os_event_wait(buf_pool->no_flush[type]);
		thd_wait_end(NULL);
	}
}

/** Do flushing batch of a given type.
NOTE: The calling thread is not allowed to own any latches on pages!
@param[in,out]	buf_pool	buffer pool instance
@param[in]	type		flush type
@param[in]	min_n		wished minimum mumber of blocks flushed
(it is not guaranteed that the actual number is that big, though)
@param[in]	lsn_limit	in the case BUF_FLUSH_LIST all blocks whose
oldest_modification is smaller than this should be flushed (if their number
does not exceed min_n), otherwise ignored
@param[out]	n_processed	the number of pages which were processed is
passed back to caller. Ignored if NULL
@retval true	if a batch was queued successfully.
@retval false	if another batch of same type was already running. */
bool
buf_flush_do_batch(
	buf_pool_t*		buf_pool,
	buf_flush_t		type,
	ulint			min_n,
	lsn_t			lsn_limit,
	ulint*			n_processed)
{
	ut_ad(type == BUF_FLUSH_LRU || type == BUF_FLUSH_LIST);

	if (n_processed != NULL) {
		*n_processed = 0;
	}

	if (!buf_flush_start(buf_pool, type)) {
		return(false);
	}

	ulint	page_count = buf_flush_batch(buf_pool, type, min_n, lsn_limit);

	buf_flush_end(buf_pool, type);

	if (n_processed != NULL) {
		*n_processed = page_count;
	}

	return(true);
}

/**
Waits until a flush batch of the given lsn ends
@param[in]	new_oldest	target oldest_modified_lsn to wait for */

void
buf_flush_wait_flushed(
	lsn_t		new_oldest)
{
	for (ulint i = 0; i < srv_buf_pool_instances; ++i) {
		buf_pool_t*	buf_pool;
		lsn_t		oldest;

		buf_pool = buf_pool_from_array(i);

		for (;;) {
			/* We don't need to wait for fsync of the flushed
			blocks, because anyway we need fsync to make chekpoint.
			So, we don't need to wait for the batch end here. */

			buf_flush_list_mutex_enter(buf_pool);

			buf_page_t*	bpage;

			/* We don't need to wait for system temporary pages */
			for (bpage = UT_LIST_GET_LAST(buf_pool->flush_list);
			     bpage != NULL
				&& fsp_is_system_temporary(bpage->id.space());
			     bpage = UT_LIST_GET_PREV(list, bpage)) {
				/* Do nothing. */
			}

			if (bpage != NULL) {
				ut_ad(bpage->in_flush_list);
				oldest = bpage->oldest_modification;
			} else {
				oldest = 0;
			}

			buf_flush_list_mutex_exit(buf_pool);

			if (oldest == 0 || oldest >= new_oldest) {
				break;
			}

			/* sleep and retry */
			os_thread_sleep(buf_flush_wait_flushed_sleep_time);

			MONITOR_INC(MONITOR_FLUSH_SYNC_WAITS);
		}
	}
}

/** This utility flushes dirty blocks from the end of the flush list of all
buffer pool instances.
NOTE: The calling thread is not allowed to own any latches on pages!
@param[in]	min_n		wished minimum mumber of blocks flushed (it is
not guaranteed that the actual number is that big, though)
@param[in]	lsn_limit	in the case BUF_FLUSH_LIST all blocks whose
oldest_modification is smaller than this should be flushed (if their number
does not exceed min_n), otherwise ignored
@param[out]	n_processed	the number of pages which were processed is
passed back to caller. Ignored if NULL.
@return true if a batch was queued successfully for each buffer pool
instance. false if another batch of same type was already running in
at least one of the buffer pool instance */
bool
buf_flush_lists(
	ulint			min_n,
	lsn_t			lsn_limit,
	ulint*			n_processed)
{
	ulint		i;
	ulint		n_flushed = 0;
	bool		success = true;

	if (n_processed) {
		*n_processed = 0;
	}

	if (min_n != ULINT_MAX) {
		/* Ensure that flushing is spread evenly amongst the
		buffer pool instances. When min_n is ULINT_MAX
		we need to flush everything up to the lsn limit
		so no limit here. */
		min_n = (min_n + srv_buf_pool_instances - 1)
			 / srv_buf_pool_instances;
	}

	/* Flush to lsn_limit in all buffer pool instances */
	for (i = 0; i < srv_buf_pool_instances; i++) {
		buf_pool_t*	buf_pool;
		ulint		page_count = 0;

		buf_pool = buf_pool_from_array(i);

		if (!buf_flush_do_batch(buf_pool,
					BUF_FLUSH_LIST,
					min_n,
					lsn_limit,
					&page_count)) {
			/* We have two choices here. If lsn_limit was
			specified then skipping an instance of buffer
			pool means we cannot guarantee that all pages
			up to lsn_limit has been flushed. We can
			return right now with failure or we can try
			to flush remaining buffer pools up to the
			lsn_limit. We attempt to flush other buffer
			pools based on the assumption that it will
			help in the retry which will follow the
			failure. */
			success = false;

			continue;
		}

		n_flushed += page_count;
	}

	if (n_flushed) {
		buf_flush_stats(n_flushed, 0);
	}

	if (n_processed) {
		*n_processed = n_flushed;
	}

	return(success);
}

/******************************************************************//**
This function picks up a single page from the tail of the LRU
list, flushes it (if it is dirty), removes it from page_hash and LRU
list and puts it on the free list. It is called from user threads when
they are unable to find a replaceable page at the tail of the LRU
list i.e.: when the background LRU flushing in the page_cleaner thread
is not fast enough to keep pace with the workload.
@return true if success. */
bool
buf_flush_single_page_from_LRU(
/*===========================*/
	buf_pool_t*	buf_pool)	/*!< in/out: buffer pool instance */
{
	ulint		scanned;
	buf_page_t*	bpage;
	ibool		freed;

	buf_pool_mutex_enter(buf_pool);

	for (bpage = buf_pool->single_scan_itr.start(), scanned = 0,
	     freed = false;
	     bpage != NULL;
	     ++scanned, bpage = buf_pool->single_scan_itr.get()) {

		ut_ad(buf_pool_mutex_own(buf_pool));

		buf_page_t*	prev = UT_LIST_GET_PREV(LRU, bpage);

		buf_pool->single_scan_itr.set(prev);

		BPageMutex*	block_mutex;

		block_mutex = buf_page_get_mutex(bpage);

		mutex_enter(block_mutex);

		if (buf_flush_ready_for_replace(bpage)) {
			/* block is ready for eviction i.e., it is
			clean and is not IO-fixed or buffer fixed. */
			mutex_exit(block_mutex);

			if (buf_LRU_free_page(bpage, true)) {
				buf_pool_mutex_exit(buf_pool);
				freed = true;
				break;
			}

		} else if (buf_flush_ready_for_flush(
				   bpage, BUF_FLUSH_SINGLE_PAGE)) {

			/* Block is ready for flush. Try and dispatch an IO
			request. We'll put it on free list in IO completion
			routine if it is not buffer fixed. The following call
			will release the buffer pool and block mutex.

			Note: There is no guarantee that this page has actually
			been freed, only that it has been flushed to disk */

			freed = buf_flush_page(
				buf_pool, bpage, BUF_FLUSH_SINGLE_PAGE, true);

			if (freed) {
				break;
			}

			mutex_exit(block_mutex);
		} else {
			mutex_exit(block_mutex);
		}

		ut_ad(!mutex_own(block_mutex));
	}

	if (!freed) {
		/* Can't find a single flushable page. */
		ut_ad(!bpage);
		buf_pool_mutex_exit(buf_pool);
	}

	if (scanned) {
		MONITOR_INC_VALUE_CUMULATIVE(
			MONITOR_LRU_SINGLE_FLUSH_SCANNED,
			MONITOR_LRU_SINGLE_FLUSH_SCANNED_NUM_CALL,
			MONITOR_LRU_SINGLE_FLUSH_SCANNED_PER_CALL,
			scanned);
	}

	ut_ad(!buf_pool_mutex_own(buf_pool));

	return(freed);
}

/**
Clears up tail of the LRU list of a given buffer pool instance:
* Put replaceable pages at the tail of LRU to the free list
* Flush dirty pages at the tail of LRU to the disk
The depth to which we scan each buffer pool is controlled by dynamic
config parameter innodb_LRU_scan_depth.
@param buf_pool buffer pool instance
@return total pages flushed */
static
ulint
buf_flush_LRU_list(
	buf_pool_t*	buf_pool)
{
	ulint	scan_depth, withdraw_depth;
	ulint	n_flushed = 0;

	ut_ad(buf_pool);

	/* srv_LRU_scan_depth can be arbitrarily large value.
	We cap it with current LRU size. */
	buf_pool_mutex_enter(buf_pool);
	scan_depth = UT_LIST_GET_LEN(buf_pool->LRU);
	if (buf_pool->curr_size < buf_pool->old_size
	    && buf_pool->withdraw_target > 0) {
		withdraw_depth = buf_pool->withdraw_target
				 - UT_LIST_GET_LEN(buf_pool->withdraw);
	} else {
		withdraw_depth = 0;
	}
	buf_pool_mutex_exit(buf_pool);

	if (withdraw_depth > srv_LRU_scan_depth) {
		scan_depth = ut_min(withdraw_depth, scan_depth);
	} else {
		scan_depth = ut_min(static_cast<ulint>(srv_LRU_scan_depth),
				    scan_depth);
	}

	/* Currently one of page_cleaners is the only thread
	that can trigger an LRU flush at the same time.
	So, it is not possible that a batch triggered during
	last iteration is still running, */
	buf_flush_do_batch(buf_pool, BUF_FLUSH_LRU, scan_depth,
			   0, &n_flushed);

	return(n_flushed);
}

/*********************************************************************//**
Clears up tail of the LRU lists:
* Put replaceable pages at the tail of LRU to the free list
* Flush dirty pages at the tail of LRU to the disk
The depth to which we scan each buffer pool is controlled by dynamic
config parameter innodb_LRU_scan_depth.
@return total pages flushed */
ulint
buf_flush_LRU_lists(void)
/*=====================*/
{
	ulint	n_flushed = 0;

	for (ulint i = 0; i < srv_buf_pool_instances; i++) {

		n_flushed += buf_flush_LRU_list(buf_pool_from_array(i));
	}

	if (n_flushed) {
		buf_flush_stats(0, n_flushed);
	}

	return(n_flushed);
}

/*********************************************************************//**
Wait for any possible LRU flushes that are in progress to end. */
void
buf_flush_wait_LRU_batch_end(void)
/*==============================*/
{
	for (ulint i = 0; i < srv_buf_pool_instances; i++) {
		buf_pool_t*	buf_pool;

		buf_pool = buf_pool_from_array(i);

		buf_pool_mutex_enter(buf_pool);

		if (buf_pool->n_flush[BUF_FLUSH_LRU] > 0
		   || buf_pool->init_flush[BUF_FLUSH_LRU]) {

			buf_pool_mutex_exit(buf_pool);
			buf_flush_wait_batch_end(buf_pool, BUF_FLUSH_LRU);
		} else {
			buf_pool_mutex_exit(buf_pool);
		}
	}
}

/*********************************************************************//**
Calculates if flushing is required based on number of dirty pages in
the buffer pool.
@return percent of io_capacity to flush to manage dirty page ratio */
/* 计算出一个刷新百分比 */
static
ulint
af_get_pct_for_dirty()
/*==================*/
{
	/* 得到 修改的块/总的块的 的百分比 记住脏数据比率 */
	double	dirty_pct = buf_get_modified_ratio_pct();

	if (dirty_pct == 0.0) {
		/* No pages modified */
		return(0);
	}

	ut_a(srv_max_dirty_pages_pct_lwm
	     <= srv_max_buf_pool_modified_pct);

	/* 如果innodb_max_dirty_pages_pct_lwm没有设置 */
	if (srv_max_dirty_pages_pct_lwm == 0) {
		/* The user has not set the option to preflush dirty
		pages as we approach the high water mark. */
		/* 如果脏数据比率大于了innodb_max_dirty_pages_pct则返回比率100% */
		if (dirty_pct >= srv_max_buf_pool_modified_pct) {
			/* We have crossed the high water mark of dirty
			pages In this case we start flushing at 100% of
			innodb_io_capacity. */
			return(100);
		}
	/* 如果设置了innodb_max_dirty_pages_pct_lwm 并且脏数据比率大于了 */	
	} else if (dirty_pct >= srv_max_dirty_pages_pct_lwm) {
		/* We should start flushing pages gradually. */
		/* innodb_max_dirty_pages_pct_lwm参数设置 */
		/* 则返回  (脏数据比率/(innodb_max_dirty_pages_pct+1))*100 也是一个比率  如(45/76)*100 */
		return(static_cast<ulint>((dirty_pct * 100)
		       / (srv_max_buf_pool_modified_pct + 1)));
	}

	return(0);
}

/*********************************************************************//**
Calculates if flushing is required based on redo generation rate.
@return percent of io_capacity to flush to manage redo space */
/* 计算出lsn的比率 百分比 */
static
ulint
af_get_pct_for_lsn(
/*===============*/
	lsn_t	age)	/*!< in: current age of LSN. */
{
	lsn_t	max_async_age;
	lsn_t	lsn_age_factor;
	/* srv_adaptive_flushing_lwm=10 那么大约就是 logtotalsize*(9/10)*(1/10) 943349 计算一个low water mark */
	lsn_t	af_lwm = (srv_adaptive_flushing_lwm
			  * log_get_capacity()) / 100;

	/* 如果当前生成的redo 小于了 low water master 则返回0 也就是说 redo日志量生成量不高则不需要权衡 */		  
	if (age < af_lwm) {
		/* No adaptive flushing. */
		/* 可以看出这里和redo设置的大小有关，如果redo文件设置越大则af_lwm越大，触发权衡的机率越小 */
		return(0);
	}

	/* 获取需要异步刷新的的位置 大约为logtotalsize*(9/10)*(7/8) */
	max_async_age = log_get_max_modified_age_async();

	/* 如果小于异步刷新 且 自适应flush 没有开启 */
	if (age < max_async_age && !srv_adaptive_flushing) {
		/* We have still not reached the max_async point and
		the user has disabled adaptive flushing. */
		return(0);
	}

	/* If we are here then we know that either:
	1) User has enabled adaptive flushing
	2) User may have disabled adaptive flushing but we have reached
	max_async_age. */
	/* /比率lsn_age_factor = (本次刷新的日志量/(logtotalsize*(9/10)*(7/8))) */
	lsn_age_factor = (age * 100) / max_async_age;

	ut_ad(srv_max_io_capacity >= srv_io_capacity);
	/* innodb_cleaner_lsn_age_factor参数默认设置为high_checkpoint */
	return(static_cast<ulint>(
		/* ((max_io_cap /io_cap) * (sqrt(lsn_age_factor)*lsn_age_factor*lsn_age_factor))/700.5 */
		/* (10 * (3.3*10*10))/700 =4.3 */
		((srv_max_io_capacity / srv_io_capacity)
		* (lsn_age_factor * sqrt((double)lsn_age_factor)))
		/ 7.5));
}

/*********************************************************************//**
This function is called approximately once every second by the
page_cleaner thread. Based on various factors it decides if there is a
need to do flushing.
@return number of pages recommended to be flushed
@param lsn_limit	pointer to return LSN up to which flushing must happen
@param last_pages_in	the number of pages flushed by the last flush_list
			flushing. */
/* 计算刷新多少个块 */			
static
ulint
page_cleaner_flush_pages_recommendation(
/*====================================*/
	lsn_t*	lsn_limit,
	ulint	last_pages_in)
{
	static	lsn_t		prev_lsn = 0;
	static	ulint		sum_pages = 0;
	static	ulint		avg_page_rate = 0;
	static	ulint		n_iterations = 0;
	static	ib_time_monotonic_t		prev_time;
	lsn_t			oldest_lsn;
	lsn_t			cur_lsn;
	lsn_t			age;
	lsn_t			lsn_rate;
	ulint			n_pages = 0;
	ulint			pct_for_dirty = 0;
	ulint			pct_for_lsn = 0;
	ulint			pct_total = 0;

	/* 获取当前的lsn 在 redo buffer中的 */
	cur_lsn = log_get_lsn();

	/* 静态变量如果是0则代表是第一次执行本函数 */
	if (prev_lsn == 0) {
		/* First time around. */
		prev_lsn = cur_lsn;
		/* 获取当前时间 */
		prev_time = ut_time_monotonic();
		return(0);
	}

	/* 如果没有redo日志生成 */
	if (prev_lsn == cur_lsn) {
		return(0);
	}

	sum_pages += last_pages_in;

	ib_time_monotonic_t	curr_time    = ut_time_monotonic();
	uint64_t	        time_elapsed = curr_time - prev_time;
	const ulong             avg_loop     = srv_flushing_avg_loops;

	/* We update our variables every srv_flushing_avg_loops
	iterations to smooth out transition in workload. */
	if (++n_iterations >= avg_loop
	    || time_elapsed >= (uint64_t)avg_loop) {

		if (time_elapsed < 1) {
			time_elapsed = 1;
		}

		/* 算出上次刷新每秒刷新的pages数量，同时加上次计算的每秒平均刷新块数 然后除以2 得到一个每秒刷新的pages数量 ！！！第一个计算条件avg_page_rate 生成 */
		avg_page_rate = static_cast<ulint>(
			((static_cast<double>(sum_pages)
			  / time_elapsed)
			 + avg_page_rate) / 2);

		/* How much LSN we have generated since last call. */
		lsn_rate = static_cast<lsn_t>(
			static_cast<double>(cur_lsn - prev_lsn)
			/ time_elapsed);

		/* 计算redo每秒平均生成率 */
		lsn_avg_rate = (lsn_avg_rate + lsn_rate) / 2;


		/* aggregate stats of all slots */
		mutex_enter(&page_cleaner->mutex);

		uint64_t  flush_tm = page_cleaner->flush_time;
		ulint	flush_pass = page_cleaner->flush_pass;

		page_cleaner->flush_time = 0;
		page_cleaner->flush_pass = 0;

		uint64_t lru_tm = 0;
		uint64_t list_tm = 0;
		ulint	lru_pass = 0;
		ulint	list_pass = 0;

		/* 扫描所有的槽 */
		for (ulint i = 0; i < page_cleaner->n_slots; i++) {
			page_cleaner_slot_t*	slot;

			slot = &page_cleaner->slots[i];

			lru_tm    += slot->flush_lru_time;
			lru_pass  += slot->flush_lru_pass;
			list_tm   += slot->flush_list_time;
			list_pass += slot->flush_list_pass;

			slot->flush_lru_time  = 0;
			slot->flush_lru_pass  = 0;
			slot->flush_list_time = 0;
			slot->flush_list_pass = 0;
		}

		mutex_exit(&page_cleaner->mutex);

		/* minimum values are 1, to avoid dividing by zero. */
		if (lru_tm < 1) {
			lru_tm = 1;
		}
		if (list_tm < 1) {
			list_tm = 1;
		}
		if (flush_tm < 1) {
			flush_tm = 1;
		}

		if (lru_pass < 1) {
			lru_pass = 1;
		}
		if (list_pass < 1) {
			list_pass = 1;
		}
		if (flush_pass < 1) {
			flush_pass = 1;
		}

		MONITOR_SET(MONITOR_FLUSH_ADAPTIVE_AVG_TIME_SLOT,
			    list_tm / list_pass);
		MONITOR_SET(MONITOR_LRU_BATCH_FLUSH_AVG_TIME_SLOT,
			    lru_tm  / lru_pass);

		MONITOR_SET(MONITOR_FLUSH_ADAPTIVE_AVG_TIME_THREAD,
			    list_tm / (srv_n_page_cleaners * flush_pass));
		MONITOR_SET(MONITOR_LRU_BATCH_FLUSH_AVG_TIME_THREAD,
			    lru_tm / (srv_n_page_cleaners * flush_pass));
		MONITOR_SET(MONITOR_FLUSH_ADAPTIVE_AVG_TIME_EST,
			    flush_tm * list_tm / flush_pass
			    / (list_tm + lru_tm));
		MONITOR_SET(MONITOR_LRU_BATCH_FLUSH_AVG_TIME_EST,
			    flush_tm * lru_tm / flush_pass
			    / (list_tm + lru_tm));
		MONITOR_SET(MONITOR_FLUSH_AVG_TIME, flush_tm / flush_pass);

		MONITOR_SET(MONITOR_FLUSH_ADAPTIVE_AVG_PASS,
			    list_pass / page_cleaner->n_slots);
		MONITOR_SET(MONITOR_LRU_BATCH_FLUSH_AVG_PASS,
			    lru_pass / page_cleaner->n_slots);
		MONITOR_SET(MONITOR_FLUSH_AVG_PASS, flush_pass);

		prev_lsn = cur_lsn;
		prev_time = curr_time;

		n_iterations = 0;

		sum_pages = 0;
	}

	/* 获取flush list中最老的ls */
	oldest_lsn = buf_pool_get_oldest_modification();

	ut_ad(oldest_lsn <= log_get_lsn());

	/* 获取当前LSN和最老LSN的之间的差值 */
	age = cur_lsn > oldest_lsn ? cur_lsn - oldest_lsn : 0;

	/* 计算出一个刷新百分比 (比如100) */
	pct_for_dirty = af_get_pct_for_dirty();
	/* 计算出lsn的比率 百分比(例如4.5) */
	pct_for_lsn = af_get_pct_for_lsn(age);

	/* 取他们的大值 */
	pct_total = ut_max(pct_for_dirty, pct_for_lsn);

	/* Estimate pages to be flushed for the lsn progress */
	/* 计算target_lsn */
	ulint	sum_pages_for_lsn = 0;
	/* 计算下一次刷新的  目标lsn 及target_lsnbuf_flush_lsn_scan_factor是定值3 */
	lsn_t	target_lsn = oldest_lsn
			     + lsn_avg_rate * buf_flush_lsn_scan_factor;

	/* 循环整个buffer instance找到小于target_lsn的脏块 */
	for (ulint i = 0; i < srv_buf_pool_instances; i++) {
		buf_pool_t*	buf_pool = buf_pool_from_array(i);
		ulint		pages_for_lsn = 0;

		buf_flush_list_mutex_enter(buf_pool);
		/* 每个innodb buffer的末尾的flush list 进行扫描，头插法? */
		for (buf_page_t* b = UT_LIST_GET_LAST(buf_pool->flush_list);
		     b != NULL;
		     b = UT_LIST_GET_PREV(list, b)) {
			if (b->oldest_modification > target_lsn) {
				break;
			}
			/* 某个 innodb buffer 实例中 flush list 小于这个  target lsn 的 page计数 */
			++pages_for_lsn;
		}
		buf_flush_list_mutex_exit(buf_pool);

		/* 这里汇总所有 innodb buffer实例中  flush list 小于这个  target lsn 的 page 总数 */
		sum_pages_for_lsn += pages_for_lsn;

		mutex_enter(&page_cleaner->mutex);
		/* 断言所有的槽处于没有刷新状态 */
		ut_ad(page_cleaner->slots[i].state
		      == PAGE_CLEANER_STATE_NONE);
		/* 确认槽的n_pages_requested值 */	  
		page_cleaner->slots[i].n_pages_requested
			= pages_for_lsn / buf_flush_lsn_scan_factor + 1;
		mutex_exit(&page_cleaner->mutex);
	}

	/* buf_flush_lsn_scan_factor为定值3 */
	sum_pages_for_lsn /= buf_flush_lsn_scan_factor;
	if(sum_pages_for_lsn < 1) {
		sum_pages_for_lsn = 1;
	}

	/* Cap the maximum IO capacity that we are going to use by
	max_io_capacity. Limit the value to avoid too quick increase */
	/* 即便是需要刷新的块数很多，最多只能刷max_io_capacity*2的数量!!!第三个计算参数生成 */
	ulint	pages_for_lsn =
		std::min<ulint>(sum_pages_for_lsn, srv_max_io_capacity * 2);

	/* PCT_IO(pct_total) 根据 前面得到的 pct_total 和 srv_io_capacity参数得到 刷新的块数 !!!第二个计算参数生成 */
	/* 3部分组成 1、根据参数计算出来的IO能力 2、以往每秒刷新页的数量 3、根据target lsn 计算出来的一个需要刷新的块数 */
	n_pages = (PCT_IO(pct_total) + avg_page_rate + pages_for_lsn) / 3;

	if (n_pages > srv_max_io_capacity) {
		n_pages = srv_max_io_capacity;
	}

	/* Normalize request for each instance */
	mutex_enter(&page_cleaner->mutex);
	ut_ad(page_cleaner->n_slots_requested == 0);
	ut_ad(page_cleaner->n_slots_flushing == 0);
	ut_ad(page_cleaner->n_slots_finished == 0);

	for (ulint i = 0; i < srv_buf_pool_instances; i++) {
		/* if REDO has enough of free space,
		don't care about age distribution of pages */
		page_cleaner->slots[i].n_pages_requested = pct_for_lsn > 30 ?
			page_cleaner->slots[i].n_pages_requested
			* n_pages / sum_pages_for_lsn + 1
			: n_pages / srv_buf_pool_instances;
	}
	mutex_exit(&page_cleaner->mutex);

	MONITOR_SET(MONITOR_FLUSH_N_TO_FLUSH_REQUESTED, n_pages);

	MONITOR_SET(MONITOR_FLUSH_N_TO_FLUSH_BY_AGE, sum_pages_for_lsn);

	MONITOR_SET(MONITOR_FLUSH_AVG_PAGE_RATE, avg_page_rate);
	MONITOR_SET(MONITOR_FLUSH_LSN_AVG_RATE, lsn_avg_rate);
	MONITOR_SET(MONITOR_FLUSH_PCT_FOR_DIRTY, pct_for_dirty);
	MONITOR_SET(MONITOR_FLUSH_PCT_FOR_LSN, pct_for_lsn);

	*lsn_limit = LSN_MAX;

	return(n_pages);
}

/*********************************************************************//**
Puts the page_cleaner thread to sleep if it has finished work in less
than a second
@retval 0 wake up by event set,
@retval OS_SYNC_TIME_EXCEEDED if timeout was exceeded
@param next_loop_time	time when next loop iteration should start
@param sig_count	zero or the value returned by previous call of
			os_event_reset() */
static
ulint
pc_sleep_if_needed(
/*===============*/
	ib_time_monotonic_ms_t		next_loop_time,
	int64_t		sig_count)
{
	ib_time_monotonic_ms_t	cur_time = ut_time_monotonic_ms();

	if (next_loop_time > cur_time) {
		/* Get sleep interval in micro seconds. We use
		ut_min() to avoid long sleep in case of wrap around. */
		int64_t sleep_us;

		sleep_us = ut_min(int64_t(1000000),
			         (next_loop_time - cur_time) * int64_t(1000));
		ut_a(sleep_us > 0);

		return(os_event_wait_time_low(buf_flush_event,
					      sleep_us, sig_count));
	}

	return(OS_SYNC_TIME_EXCEEDED);
}

/******************************************************************//**
Initialize page_cleaner. */
void
buf_flush_page_cleaner_init(void)
/*=============================*/
{
	ut_ad(page_cleaner == NULL);

	page_cleaner = static_cast<page_cleaner_t*>(
		ut_zalloc_nokey(sizeof(*page_cleaner)));

	mutex_create(LATCH_ID_PAGE_CLEANER, &page_cleaner->mutex);

	page_cleaner->is_requested = os_event_create("pc_is_requested");
	page_cleaner->is_finished = os_event_create("pc_is_finished");

	page_cleaner->n_slots = static_cast<ulint>(srv_buf_pool_instances);

	page_cleaner->slots = static_cast<page_cleaner_slot_t*>(
		ut_zalloc_nokey(page_cleaner->n_slots
				* sizeof(*page_cleaner->slots)));

	ut_d(page_cleaner->n_disabled_debug = 0);

	page_cleaner->is_running = true;
}

/**
Close page_cleaner. */
static
void
buf_flush_page_cleaner_close(void)
{
	/* waiting for all worker threads exit */
	while (page_cleaner->n_workers > 0) {
		os_thread_sleep(10000);
	}

	mutex_destroy(&page_cleaner->mutex);

	ut_free(page_cleaner->slots);

	os_event_destroy(page_cleaner->is_finished);
	os_event_destroy(page_cleaner->is_requested);

	ut_free(page_cleaner);

	page_cleaner = NULL;
}

/**
Requests for all slots to flush all buffer pool instances.
@param min_n	wished minimum mumber of blocks flushed
		(it is not guaranteed that the actual number is that big)
@param lsn_limit in the case BUF_FLUSH_LIST all blocks whose
		oldest_modification is smaller than this should be flushed
		(if their number does not exceed min_n), otherwise ignored
*/
/*  
	为每个slot代表的缓冲池实例计算要刷脏多少页；
	然后把每个slot的state设置PAGE_CLEANER_STATE_REQUESTED；
	把n_slots_requested设置成当前slots的总数，也即缓冲池实例的个数，
	同时把n_slots_flushing和n_slots_finished清0，
	然后唤醒等待的工作线程 
*/
static
void
pc_request(
	ulint		min_n,
	lsn_t		lsn_limit)
{
	if (min_n != ULINT_MAX) {
		/* Ensure that flushing is spread evenly amongst the
		buffer pool instances. When min_n is ULINT_MAX
		we need to flush everything up to the lsn limit
		so no limit here. */
		min_n = (min_n + srv_buf_pool_instances - 1)
			/ srv_buf_pool_instances;
	}

	/* 由于page_cleaner是全局的，在修改之前先获取互斥锁 */
	mutex_enter(&page_cleaner->mutex);

	ut_ad(page_cleaner->n_slots_requested == 0);
	ut_ad(page_cleaner->n_slots_flushing == 0);
	ut_ad(page_cleaner->n_slots_finished == 0);

	/* 是否需要对flush_list进行刷脏操作，还是只需要对LRU列表刷脏 */
	page_cleaner->requested = (min_n > 0);
	/* 设置lsn_limit, 只有数据页的oldest_modification小于它的才会刷出去 */
	page_cleaner->lsn_limit = lsn_limit;

	/* 逐个的指向维护 */
	for (ulint i = 0; i < page_cleaner->n_slots; i++) {
		page_cleaner_slot_t* slot = &page_cleaner->slots[i];

		ut_ad(slot->state == PAGE_CLEANER_STATE_NONE);

		/* 
			为两种特殊情况设置每个slot需要刷脏的页数，
				当为ULINT_MAX表示服务器比较空闲，则刷脏线程可以尽可能的把当前的所有脏页都刷出去；
				而当为0是，表示没有脏页可刷 
		*/
		if (min_n == ULINT_MAX) {
			slot->n_pages_requested = ULINT_MAX;
		} else if (min_n == 0) {
			slot->n_pages_requested = 0;
		}

		/* slot->n_pages_requested was already set by
		page_cleaner_flush_pages_recommendation() */

		/* 在唤醒刷脏工作线程之前，将每个slot的状态设置成requested状态 */
		slot->state = PAGE_CLEANER_STATE_REQUESTED;
	}

	/* 
		协调线程在唤醒工作线程之前，设置请求要刷脏的slot个数，以及清空正在刷脏和完成刷脏的slot个数。
		只有当完成的刷脏个数等于总的slot个数时，才表示次轮的刷脏结束。 
	*/
	page_cleaner->n_slots_requested = page_cleaner->n_slots;
	page_cleaner->n_slots_flushing = 0;
	page_cleaner->n_slots_finished = 0;

	/* 这会唤起page cleaner worker线程 */
	os_event_set(page_cleaner->is_requested);

	mutex_exit(&page_cleaner->mutex);
}

/**
Do flush for one slot.
@return	the number of the slots which has not been treated yet. */
/* 
	实际执行刷新的函数 
	协调线程和工作线程都会执行

	由于刷脏线程和slot并不是事先绑定对应的关系。
	所以工作线程在刷脏时：
		首先会找到一个未被占用的slot，修改其状态，表示已被调度，
		然后对该slot所对应的缓冲池instance进行操作。直到所有的slot都被消费完后，才进入下一轮。
		通过这种方式，多个刷脏线程实现了并发刷脏缓冲池。
		一旦找到一个未被占用的slot，则需要把全局的page_cleaner里的n_slots_rqeusted减1、把n_slots_flushing加1，
		同时这个slot的状态从PAGE_CLEANER_STATE_REQUESTED状态改成PAGE_CLEANER_STATE_FLUSHING。
		然后分别调用buf_flush_LRU_list() 和buf_flush_do_batch() 对LRU和flush_list刷脏。
		刷脏结束把n_slots_flushing减1，把n_slots_finished加1，同时把这个slot的状态从PAGE_CLEANER_STATE_FLUSHING状态改成PAGE_CLEANER_STATE_FINISHED状态。
		同时若这个工作线程是最后一个完成的，则需要通过is_finished事件，通知协调进程所有的工作线程刷脏结束。
*/
static
ulint
pc_flush_slot(void)
{
	ib_time_monotonic_ms_t	lru_tm = 0;
	ib_time_monotonic_ms_t	list_tm = 0;
	int	lru_pass = 0;
	int	list_pass = 0;

	mutex_enter(&page_cleaner->mutex);

	if (page_cleaner->n_slots_requested > 0) {
		page_cleaner_slot_t*	slot = NULL;
		ulint			i;

		/* 以下这个遍历其实就是在找出需要刷脏的slot的索引 */
		/* 由于slot和刷脏线程不是事先定好的一一对应关系，所以在每个工作线程开始要 先找到一个未被处理的slot */
		for (i = 0; i < page_cleaner->n_slots; i++) {
			slot = &page_cleaner->slots[i];

			if (slot->state == PAGE_CLEANER_STATE_REQUESTED) {
				break;
			}
		}

		/* slot should be found because
		page_cleaner->n_slots_requested > 0 */
		ut_a(i < page_cleaner->n_slots);

		/* 根据找到的slot，对应其缓冲池的实例 */
		buf_pool_t* buf_pool = buf_pool_from_array(i);

		/* 表明这个slot开始被处理，将未被处理的slot数减1 */
		page_cleaner->n_slots_requested--;
		/* 这个slot开始刷脏，将flushing加1 */
		page_cleaner->n_slots_flushing++;
		/* 把这个slot的状态设置为flushing状态，保证不会被其它工作线程挑选 */
		slot->state = PAGE_CLEANER_STATE_FLUSHING;

		/* 若是所有的slot都处理了，则清除is_requested的通知标志 */
		if (page_cleaner->n_slots_requested == 0) {
			os_event_reset(page_cleaner->is_requested);
		}

		if (!page_cleaner->is_running) {
			slot->n_flushed_lru = 0;
			slot->n_flushed_list = 0;
			goto finish_mutex;
		}

		mutex_exit(&page_cleaner->mutex);

		lru_tm = ut_time_monotonic_ms();

		/* Flush pages from end of LRU if required */
		/* 刷LRU队列，并且记录LRU冲刷的页数 */
		slot->n_flushed_lru = buf_flush_LRU_list(buf_pool);

		lru_tm = ut_time_monotonic_ms() - lru_tm;
		lru_pass++;

		if (!page_cleaner->is_running) {
			slot->n_flushed_list = 0;
			goto finish;
		}

		/* Flush pages from flush_list if required */
		/* 刷flush_list队列 */
		if (page_cleaner->requested) {

			list_tm = ut_time_monotonic_ms();

			slot->succeeded_list = buf_flush_do_batch(
				buf_pool, BUF_FLUSH_LIST,
				slot->n_pages_requested,
				page_cleaner->lsn_limit,
				&slot->n_flushed_list);

			list_tm = ut_time_monotonic_ms() - list_tm;
			list_pass++;
		} else {
			slot->n_flushed_list = 0;
			slot->succeeded_list = true;
		}
finish:
		mutex_enter(&page_cleaner->mutex);
finish_mutex:
		/* 刷脏工作线程完成次轮刷脏后，将flushing减1 */
		page_cleaner->n_slots_flushing--;
		/* 刷脏工作线程完成次轮刷脏后，将完成的slot加一 */
		page_cleaner->n_slots_finished++;
		/* 设置此slot的状态为FINISHED */
		slot->state = PAGE_CLEANER_STATE_FINISHED;

		slot->flush_lru_time += lru_tm;
		slot->flush_list_time += list_tm;
		slot->flush_lru_pass += lru_pass;
		slot->flush_list_pass += list_pass;

		if (page_cleaner->n_slots_requested == 0
		    && page_cleaner->n_slots_flushing == 0) {
			/* 当所有的工作线程都完成了刷脏，要通知协调进程，本轮刷脏完成 */	
			os_event_set(page_cleaner->is_finished);
		}
	}

	ulint	ret = page_cleaner->n_slots_requested;

	mutex_exit(&page_cleaner->mutex);

	return(ret);
}

/**
Wait until all flush requests are finished.
@param n_flushed_lru	number of pages flushed from the end of the LRU list.
@param n_flushed_list	number of pages flushed from the end of the
			flush_list.
@return			true if all flush_list flushing batch were success. */
/*  
	主要由协调线程调用，它主要用来收集每个工作线程分别对LRU和flush_list列表刷脏的页数。以及为每个slot清0次轮请求刷脏的页数和重置它的状态为NONE
*/
static
bool
pc_wait_finished(
	ulint*	n_flushed_lru,
	ulint*	n_flushed_list)
{
	bool	all_succeeded = true;

	*n_flushed_lru = 0;
	*n_flushed_list = 0;

	/* 协调线程通知工作线程和完成自己的刷脏任务之后，要等在is_finished事件上，知道最后一个完成的工作线程会set这个事件唤醒协调线程 */
	os_event_wait(page_cleaner->is_finished);

	mutex_enter(&page_cleaner->mutex);

	ut_ad(page_cleaner->n_slots_requested == 0);
	ut_ad(page_cleaner->n_slots_flushing == 0);
	ut_ad(page_cleaner->n_slots_finished == page_cleaner->n_slots);

	for (ulint i = 0; i < page_cleaner->n_slots; i++) {
		page_cleaner_slot_t* slot = &page_cleaner->slots[i];

		ut_ad(slot->state == PAGE_CLEANER_STATE_FINISHED);

		/* 统计每个slot分别通过LRU和flush_list队列刷出去的页数 */
		*n_flushed_lru += slot->n_flushed_lru;
		*n_flushed_list += slot->n_flushed_list;
		all_succeeded &= slot->succeeded_list;

		/* 把所有slot的状态设置为NONE */
		slot->state = PAGE_CLEANER_STATE_NONE;

		/* 为每个slot清除请求刷脏的页数 */
		slot->n_pages_requested = 0;
	}

	/* 清零完成的slot刷脏个数，为下一轮刷脏重新统计做准备 */
	page_cleaner->n_slots_finished = 0;

	/* 清除is_finished事件的通知标志 */
	os_event_reset(page_cleaner->is_finished);

	mutex_exit(&page_cleaner->mutex);

	return(all_succeeded);
}

#ifdef UNIV_LINUX
/**
Set priority for page_cleaner threads.
@param[in]	priority	priority intended to set
@return	true if set as intended */
static
bool
buf_flush_page_cleaner_set_priority(
	int	priority)
{
	setpriority(PRIO_PROCESS, (pid_t)syscall(SYS_gettid),
		    priority);
	return(getpriority(PRIO_PROCESS, (pid_t)syscall(SYS_gettid))
	       == priority);
}
#endif /* UNIV_LINUX */

#ifdef UNIV_DEBUG
/** Loop used to disable page cleaner threads. */
static
void
buf_flush_page_cleaner_disabled_loop(void)
{
	ut_ad(page_cleaner != NULL);

	if (!innodb_page_cleaner_disabled_debug) {
		/* We return to avoid entering and exiting mutex. */
		return;
	}

	mutex_enter(&page_cleaner->mutex);
	page_cleaner->n_disabled_debug++;
	mutex_exit(&page_cleaner->mutex);

	while (innodb_page_cleaner_disabled_debug
	       && srv_shutdown_state == SRV_SHUTDOWN_NONE
	       && page_cleaner->is_running) {

		os_thread_sleep(100000); /* [A] */
	}

	/* We need to wait for threads exiting here, otherwise we would
	encounter problem when we quickly perform following steps:
		1) SET GLOBAL innodb_page_cleaner_disabled_debug = 1;
		2) SET GLOBAL innodb_page_cleaner_disabled_debug = 0;
		3) SET GLOBAL innodb_page_cleaner_disabled_debug = 1;
	That's because after step 1 this thread could still be sleeping
	inside the loop above at [A] and steps 2, 3 could happen before
	this thread wakes up from [A]. In such case this thread would
	not re-increment n_disabled_debug and we would be waiting for
	him forever in buf_flush_page_cleaner_disabled_debug_update(...).

	Therefore we are waiting in step 2 for this thread exiting here. */

	mutex_enter(&page_cleaner->mutex);
	page_cleaner->n_disabled_debug--;
	mutex_exit(&page_cleaner->mutex);
}

/** Disables page cleaner threads (coordinator and workers).
It's used by: SET GLOBAL innodb_page_cleaner_disabled_debug = 1 (0).
@param[in]	thd		thread handle
@param[in]	var		pointer to system variable
@param[out]	var_ptr		where the formal string goes
@param[in]	save		immediate result from check function */
void
buf_flush_page_cleaner_disabled_debug_update(
	THD*				thd,
	struct st_mysql_sys_var*	var,
	void*				var_ptr,
	const void*			save)
{
	if (page_cleaner == NULL) {
		return;
	}

	if (!*static_cast<const my_bool*>(save)) {
		if (!innodb_page_cleaner_disabled_debug) {
			return;
		}

		innodb_page_cleaner_disabled_debug = false;

		/* Enable page cleaner threads. */
		while (srv_shutdown_state == SRV_SHUTDOWN_NONE) {
			mutex_enter(&page_cleaner->mutex);
			const ulint n = page_cleaner->n_disabled_debug;
			mutex_exit(&page_cleaner->mutex);
			/* Check if all threads have been enabled, to avoid
			problem when we decide to re-disable them soon. */
			if (n == 0) {
				break;
			}
		}
		return;
	}

	if (innodb_page_cleaner_disabled_debug) {
		return;
	}

	innodb_page_cleaner_disabled_debug = true;

	while (srv_shutdown_state == SRV_SHUTDOWN_NONE) {
		/* Workers are possibly sleeping on is_requested.

		We have to wake them, otherwise they could possibly
		have never noticed, that they should be disabled,
		and we would wait for them here forever.

		That's why we have sleep-loop instead of simply
		waiting on some disabled_debug_event. */
		os_event_set(page_cleaner->is_requested);

		mutex_enter(&page_cleaner->mutex);

		ut_ad(page_cleaner->n_disabled_debug
		      <= srv_n_page_cleaners);

		if (page_cleaner->n_disabled_debug
		    == srv_n_page_cleaners) {

			mutex_exit(&page_cleaner->mutex);
			break;
		}

		mutex_exit(&page_cleaner->mutex);

		os_thread_sleep(100000);
	}
}
#endif /* UNIV_DEBUG */

/******************************************************************//**
page_cleaner thread tasked with flushing dirty pages from the buffer
pools. As of now we'll have only one coordinator.
@return a dummy parameter */
/*  
	buffer pool是通过三种list来管理的
		1 free list
		2 lru list
		3 flush list

	buffer pool中的最小单位是page，在innodb中定义三种page
		1 free page
			此page未被使用，此种类型page位于free链表中
		2 clean page
			此page被使用，对应数据文件中的一个页面，但是页面没有被修改，此种类型page位于lru链表中
		3 dirty page
			此page被使用，对应数据文件中的一个页面，但是页面被修改过，此种类型page位于lru链表和flush链表中

	flush list  ----[]----[]----[]----[]----[]----[]---->
					↓ 指针		↓ 指针
	lru list    ----[]----[]----[]----[]----[]----[]---->
							↓	转换	  ↑ 转换	
	free list   ----[]----[]----[]----[]----[]----[]---->

	当buffer pool不够用时，根据lru机制，mysql会将old sublist部分的缓存页移出lru链表。
	如果被移除出去的缓存页的描述信息在flush list中，mysql就得将其刷新回磁盘。

	在flush list中存在的page只能是dirty page，flush list中存在的dirty page是按着oldest_modification时间排序的，
	当页面访问/修改都被封装为一个mini-transaction，mini-transactin提交的时候，则mini-transaction涉及到的页面就进入了flush链表中，
	oldest_modification的值越大，说明page越晚被修改过，就排在flush链表的头部，
	oldest_modification的值越小，说明page越早被修改过，就排在flush链表的尾部，
	这样当flush链表做flush动作时，从flush链表的尾部开始scan，写出一定数量的dirty page到磁盘，推进checkpoint点，使恢复的时间尽可能的短。
	
	除了flush链表本身的flush操作可以把dirty page从flush链表删除外，lru链表的flush操作也会让dirty page从flush链表删除。

	Flush LRU 与 Flush FLUSH_LIST 区别
		1、	LRU list flush，其目的是为了写出LRU 链表尾部的dirty page，释放足够的free pages，当buf pool满的时候，用户可以立即获得空闲页面，而不需要长时间等待；
			Flush list flush，其目的是推进Checkpoint LSN，使得InnoDB系统崩溃之后能够快速的恢复。
		2、	LRU list flush，其写出的dirty page，是直接从LRU链表中删除，移动到free list(MySQL 5.6.2之后版本)。
			Flush list flush，不需要移动page在LRU链表中的位置。
		3、	LRU list flush，每次flush的dirty pages数量较少，基本固定，只要释放一定的free pages即可；
			Flush list flush，根据当前系统的更新繁忙程度，动态调整一次flush的dirty pages数量，量很大。

	查看LRU中的页
		select table_name,space,page_number,page_type from information_schema.innodb_buffer_page_lru ;
			+--------------------------------------------------------------------------+-------+-------------+-------------------+
			| table_name                                                               | space | page_number | page_type         |
			+--------------------------------------------------------------------------+-------+-------------+-------------------+
			| NULL                                                                     |     0 |           3 | SYSTEM            |
			| NULL                                                                     |     8 |           1 | IBUF_BITMAP       |
			| NULL                                                                     |     8 |           2 | INODE             |
			| `mysql`.`time_zone_name`                                                 |     8 |           3 | INDEX             |
			| NULL                                                                     |    16 |           1 | IBUF_BITMAP       |
			| NULL                                                                     |    16 |           2 | INODE             |
			| `mysql`.`slave_master_info`                                              |    16 |           3 | INDEX             |
			| NULL                                                                     |   240 |           1 | IBUF_BITMAP       |

	查看脏页
		select table_name,space,page_number,page_type from information_schema.innodb_buffer_page_lru where oldest_modification>0;
			1+--------------+-------+-------------+-----------+
			| table_name   | space | page_number | page_type |
			+--------------+-------+-------------+-----------+
			| `SYS_TABLES` |   433 |          64 | INDEX     |
			| `SYS_TABLES` |   433 |          65 | INDEX     |
			| `SYS_TABLES` |   433 |          66 | INDEX     |
			| `SYS_TABLES` |   433 |          67 | INDEX     |
			| `SYS_TABLES` |   433 |        1280 | INDEX     |

*/
/*  
DECLARE_THREAD(buf_flush_page_cleaner_coordinator)          协调线程
    |__my_thread_init
    |----InnoDB从崩溃中恢复时的处理   
    |__while (!srv_read_only_mode && srv_shutdown_state == SRV_SHUTDOWN_NONE && recv_sys->heap != NULL)
    |   |__os_event_wait(recv_sys->flush_start)
    |   |__pc_request(0, LSN_MAX)                   只刷新LRU，为每个slot计算要刷多少页，实际页数在page_cleaner_flush_pages_recommendation计算
    |   |   |__os_event_set(page_cleaner->is_requested)       这会唤起page cleaner worker线程，工作线程会调用pc_flush_slot执行刷新 
    |   |__pc_request(ULINT_MAX, LSN_MAX)           刷新LRU和FLUSH LIST，为每个slot计算要刷多少页
    |   |   |__os_event_set(page_cleaner->is_requested)
    |   |__pc_flush_slot()                  实际刷新
    |   |__pc_wait_finished(&n_flushed_lru, &n_flushed_list)
    |----一般情况下的处理
    |__while (srv_shutdown_state == SRV_SHUTDOWN_NONE)          
    |   |-------检测是否需要睡眠1秒-----------------------------------------------------------------------------------------------    
    |   |__if (srv_check_activity(last_activity)|| buf_get_n_pending_read_ios() || n_flushed == 0)    是否需要睡眠1秒判断，如果有有活跃的线程、或有pending的物理块、或上次刷新的块数量为0，则睡眠1秒
    |   |   |__pc_sleep_if_needed                                   休眠min(1000000,(next_loop_time-当前时间)*1000))
    |   |__else if (ut_time_monotonic_ms() > next_loop_time)        如果当前时间大于 上次刷新 时间+1 秒则 设置为OS_SYNC_TIME_EXCEEDED
    |   |__else
    |   |-------检测是否需要输出IO能力不足警告-----------------------------------------------------------------------------------------------        
    |   |__if (ret_sleep == OS_SYNC_TIME_EXCEEDED)                  如果当前时间 大于 上次刷新时间+1秒 则判断是否需要输出IO能力不足警告
    |   |   |__if (curr_time > next_loop_time + 3000)                   如果刷新时间 大于了 上次时间 +1 秒+3 秒 则报info，即IO能力不足警告
    |   |-------同步刷新---------------------------------------------------------------------------------------------------------------------
    |   |__if (ret_sleep != OS_SYNC_TIME_EXCEEDED && srv_flush_sync && buf_flush_sync_lsn > 0)         
    |   |   |__pc_request(ULINT_MAX, lsn_limit)    唤起工作线程刷新
    |   |   |__pc_flush_slot()                     协调线程自己也需要刷新
    |   |   |__pc_wait_finished
    |   |-------活跃刷新---------------------------------------------------------------------------------------------------------------------
    |   |__else if (srv_check_activity(last_activity))
    |   |   |__page_cleaner_flush_pages_recommendation      计算刷新多少个块
    |   |   |__pc_request(n_to_flush, lsn_limit)
    |   |   |__pc_flush_slot
    |   |   |__pc_wait_finished
    |   |-------空闲刷新---------------------------------------------------------------------------------------------------------------------
    |   |__else if (ret_sleep == OS_SYNC_TIME_EXCEEDED)
    |       |__buf_flush_lists(PCT_IO(100), LSN_MAX, &n_flushed)
    |           |__buf_flush_do_batch
    |----InnoDB正常关闭情况下的处理
    |__do while (srv_shutdown_state == SRV_SHUTDOWN_CLEANUP)
    |   |__pc_request(ULINT_MAX, LSN_MAX)
    |   |__pc_flush_slot
    |   |__pc_wait_finished
    |__buf_flush_wait_batch_end
    |__buf_flush_wait_LRU_batch_end
    |__do while (!success || n_flushed > 0)
        |__pc_request(ULINT_MAX, LSN_MAX)
        |__pc_flush_slot
        |__pc_wait_finished
        |__pc_wait_finished
*/
/* page cleaner线程从buffer pool中刷脏页 */
extern "C"
os_thread_ret_t
DECLARE_THREAD(buf_flush_page_cleaner_coordinator)(
/*===============================================*/
	void*	arg MY_ATTRIBUTE((unused)))
			/*!< in: a dummy parameter required by
			os_thread_create */
{
	ib_time_monotonic_t	next_loop_time = ut_time_monotonic_ms() + 1000;
	ulint	n_flushed = 0;
	ulint	last_activity = srv_get_activity_count();
	ulint	last_pages = 0;

	my_thread_init();

#ifdef UNIV_PFS_THREAD
	pfs_register_thread(page_cleaner_thread_key);
#endif /* UNIV_PFS_THREAD */

#ifdef UNIV_DEBUG_THREAD_CREATION
	ib::info() << "page_cleaner thread running, id "
		<< os_thread_pf(os_thread_get_curr_id());
#endif /* UNIV_DEBUG_THREAD_CREATION */

#ifdef UNIV_LINUX
	/* linux might be able to set different setting for each thread.
	worth to try to set high priority for page cleaner threads */
	if (buf_flush_page_cleaner_set_priority(
		buf_flush_page_cleaner_priority)) {

		ib::info() << "page_cleaner coordinator priority: "
			<< buf_flush_page_cleaner_priority;
	} else {
		ib::info() << "If the mysqld execution user is authorized,"
		" page cleaner thread priority can be changed."
		" See the man page of setpriority().";
	}
#endif /* UNIV_LINUX */

	buf_page_cleaner_is_active = true;

	/* 
--------------------------------------------------------------------------------------------------------------
		InnoDB从崩溃中恢复时的处理 
		recv_sys为在崩溃恢复前滚阶段使用的内存结构
	*/
	while (!srv_read_only_mode
	       && srv_shutdown_state == SRV_SHUTDOWN_NONE
	       && recv_sys->heap != NULL) {
		/* treat flushing requests during recovery. */
		ulint	n_flushed_lru = 0;
		ulint	n_flushed_list = 0;

		os_event_wait(recv_sys->flush_start);

		/* 服务器没有关闭的状态下 */
		if (srv_shutdown_state != SRV_SHUTDOWN_NONE
		    || recv_sys->heap == NULL) {
			break;
		}

		switch (recv_sys->flush_type) {	
		/* 刷新LRU脏页 */	
		case BUF_FLUSH_LRU:
			/* Flush pages from end of LRU if required */
			/* 
				为每个slot代表的缓冲池实例计算要刷脏多少页；
				然后把每个slot的state设置PAGE_CLEANER_STATE_REQUESTED；
				把n_slots_requested设置成当前slots的总数，也即缓冲池实例的个数，
				同时把n_slots_flushing和n_slots_finished清0，
				然后唤醒等待的工作线程 
			*/
			pc_request(0, LSN_MAX);
			/* 
				实际执行刷新的函数 
				协调线程和工作线程都会执行
			*/
			while (pc_flush_slot() > 0) {}
			/*  
				主要由协调线程调用，它主要用来收集每个工作线程分别对LRU和flush_list列表刷脏的页数。
				以及为每个slot清0次轮请求刷脏的页数和重置它的状态为NONE
			*/
			pc_wait_finished(&n_flushed_lru, &n_flushed_list);
			break;

		/* 刷新FLUSH_LIST脏页 */
		case BUF_FLUSH_LIST:
			/* Flush all pages */
			do {
				pc_request(ULINT_MAX, LSN_MAX);
				while (pc_flush_slot() > 0) {}
			} while (!pc_wait_finished(&n_flushed_lru,
						   &n_flushed_list));
			break;

		default:
			ut_ad(0);
		}

		os_event_reset(recv_sys->flush_start);
		os_event_set(recv_sys->flush_end);
	}

	os_event_wait(buf_flush_event);

	ulint		ret_sleep = 0;
	ulint		n_evicted = 0;
	ulint		n_flushed_last = 0;
	ulint		warn_interval = 1;
	ulint		warn_count = 0;
	int64_t		sig_count = os_event_reset(buf_flush_event);

	/*
--------------------------------------------------------------------------------------------------------------
		一般情况下的处理	  
	
	recovery处理完之后，协调线程进入日常执行的阶段，开始等待buf_flush_event。os_event_set(buf_flush_event)将唤醒page cleaner来flush脏页。
	有以下五个时机：
		prepareSpace btr0bulk.cc 索引构建时
		buf_LRU_get_free_block buf0lru.cc 为了分配空闲块而调用
		buf_flush_request_force buf0flu.cc 这里是同步的flush请求，在做检查点时调用。
		srv_shutdown_all_bg_threads srv0start.cc 关闭所有innodb后台线程
		srv_start srv0start.cc 启动时
		srv_shutdown_page_cleaners srv0start.cc 关闭innodb database时调用
		我们从上面可以看出flush活动出现的时机。

	首先调用pc_sleep_if_needed判断要睡多久，首先对返回值ret_sleep做处理。 
	ret_sleep == OS_SYNC_TIME_EXCEEDED 如果超时，则会重新计算下次sleep的时间。
	*/
	while (srv_shutdown_state == SRV_SHUTDOWN_NONE) {
		/* 这个睡眠是可以被唤醒的，比如同步刷新应该就会唤醒它（buf_flush_request_force函数）。参考函数os_event::wait_time_low */

		/* The page_cleaner skips sleep if the server is
		idle and there are no pending IOs in the buffer pool
		and there is work to do. */
		/*  
			是否需要睡眠1秒判断
			如果有有活跃的线程、或有pending的物理块、或上次刷新的块数量为0，则睡眠1秒
		*/
		if (srv_check_activity(last_activity)
		    || buf_get_n_pending_read_ios()
		    || n_flushed == 0) {
			/* 休眠min(1000000,(next_loop_time-当前时间)*1000)) */	
			ret_sleep = pc_sleep_if_needed(
				next_loop_time, sig_count);

			if (srv_shutdown_state != SRV_SHUTDOWN_NONE) {
				break;
			}
		/* 如果当前时间 大于 上次刷新时间+1秒 则设置为OS_SYNC_TIME_EXCEEDED */
		} else if (ut_time_monotonic_ms() > next_loop_time) {
			ret_sleep = OS_SYNC_TIME_EXCEEDED;
		} else {
			ret_sleep = 0;
		}

		sig_count = os_event_reset(buf_flush_event);

		/*  
			如果当前时间 大于 上次刷新时间+1秒 则判断是否需要输出IO能力不足警告
		*/
		if (ret_sleep == OS_SYNC_TIME_EXCEEDED) {
			ib_time_monotonic_ms_t curr_time =
						ut_time_monotonic_ms();

			/* 如果刷新时间 大于 上次时间 +1 秒+3 秒 则输出IO能力不足警告 */
			if (curr_time > next_loop_time + 3000) {
				if (warn_count == 0) {
					ib::info() << "page_cleaner: 1000ms"
						" intended loop took "
						<< 1000 + curr_time
						   - next_loop_time
						<< "ms. The settings might not"
						" be optimal. (flushed="
						<< n_flushed_last
						<< " and evicted="
						<< n_evicted
						<< ", during the time.)";
					if (warn_interval > 300) {
						warn_interval = 600;
					} else {
						warn_interval *= 2;
					}

					warn_count = warn_interval;
				} else {
					--warn_count;
				}
			} else {
				/* reset counter */
				warn_interval = 1;
				warn_count = 0;
			}

			/* 重新计算当前next_loop_time值 */
			next_loop_time = curr_time + 1000;
			n_flushed_last = n_evicted = 0;
		}

		/*  
			--------------------------------------------------------------------------------------------
			同步刷新 
			同步会唤醒正在睡眠状态的page clean协调工作线程那么睡眠应该不会满足一秒的条件所以不会被标记为OS_SYNC_TIME_EXCEEDED，
			同时srv_flush_sync和buf_flush_sync_lsn均会被设置接下来就是唤醒工作线程进行刷新，同时本协调线程也完成部分任务。

			这是同步flush的请求，如果到了同步阶段，所有活动都停下等这个同步的flush完成。包括协调器线程本身，也参与到flush工作中来。
		*/
		if (ret_sleep != OS_SYNC_TIME_EXCEEDED
		    && srv_flush_sync
		    && buf_flush_sync_lsn > 0) {
			/* woke up for flush_sync */
			mutex_enter(&page_cleaner->mutex);
			lsn_t	lsn_limit = buf_flush_sync_lsn;
			buf_flush_sync_lsn = 0;
			mutex_exit(&page_cleaner->mutex);

			/* Request flushing for threads */
			/* 
				为每个slot代表的缓冲池实例计算要刷脏多少页；
				然后把每个slot的state设置PAGE_CLEANER_STATE_REQUESTED；
				把n_slots_requested设置成当前slots的总数，也即缓冲池实例的个数，
				同时把n_slots_flushing和n_slots_finished清0，
				然后唤醒等待的工作线程 
			*/
			/* 唤醒page clean 工作线程干活 */
			pc_request(ULINT_MAX, lsn_limit);

			ib_time_monotonic_ms_t tm = ut_time_monotonic_ms();

			/* Coordinator also treats requests */
			/* 
				实际执行刷新的函数 
				协调线程和工作线程都会执行
			*/
			/* 协调者同样要完成部分任务 */
			while (pc_flush_slot() > 0) {}

			/* only coordinator is using these counters,
			so no need to protect by lock. */
			page_cleaner->flush_time += ut_time_monotonic_ms() - tm;
			page_cleaner->flush_pass++;

			/* Wait for all slots to be finished */
			ulint	n_flushed_lru = 0;
			ulint	n_flushed_list = 0;
			/*  
				主要由协调线程调用，它主要用来收集每个工作线程分别对LRU和flush_list列表刷脏的页数。
				以及为每个slot清0次轮请求刷脏的页数和重置它的状态为NONE
			*/
			pc_wait_finished(&n_flushed_lru, &n_flushed_list);

			if (n_flushed_list > 0 || n_flushed_lru > 0) {
				buf_flush_stats(n_flushed_list, n_flushed_lru);

				MONITOR_INC_VALUE_CUMULATIVE(
					MONITOR_FLUSH_SYNC_TOTAL_PAGE,
					MONITOR_FLUSH_SYNC_COUNT,
					MONITOR_FLUSH_SYNC_PAGES,
					n_flushed_lru + n_flushed_list);
			}

			n_flushed = n_flushed_lru + n_flushed_list;

		/*  
			--------------------------------------------------------------------------------------------
			活跃刷新

			这时是说明有其他活动在进行，那么调用page_cleaner_flush_pages_recommendation计算要flush的page数目，这里就是adaptive flushing算法的所在。
			关于自适应刷新的有关参数，则是在af_get_pct_for_dirty中计算，并且根据配置的IO能力在page_cleaner_flush_pages_recommendation中设置了下次flush的目标。
		*/
		} else if (srv_check_activity(last_activity)) {   /* 是否有活跃的线程 */
			ulint	n_to_flush;
			lsn_t	lsn_limit = 0;

			/* Estimate pages from flush_list to be flushed */
			if (ret_sleep == OS_SYNC_TIME_EXCEEDED) {
				last_activity = srv_get_activity_count();
				n_to_flush =
					/* 计算刷新多少个块 */
					page_cleaner_flush_pages_recommendation(
						&lsn_limit, last_pages);
			} else {
				n_to_flush = 0;
			}

			/* Request flushing for threads */
			pc_request(n_to_flush, lsn_limit);

			ib_time_monotonic_ms_t tm = ut_time_monotonic_ms();

			/* Coordinator also treats requests */
			while (pc_flush_slot() > 0) {
				/* No op */
			}

			/* only coordinator is using these counters,
			so no need to protect by lock. */
			page_cleaner->flush_time += ut_time_monotonic_ms() - tm;
			page_cleaner->flush_pass++ ;

			/* Wait for all slots to be finished */
			ulint	n_flushed_lru = 0;
			ulint	n_flushed_list = 0;

			pc_wait_finished(&n_flushed_lru, &n_flushed_list);

			if (n_flushed_list > 0 || n_flushed_lru > 0) {
				buf_flush_stats(n_flushed_list, n_flushed_lru);
			}

			if (ret_sleep == OS_SYNC_TIME_EXCEEDED) {
				last_pages = n_flushed_list;
			}

			n_evicted += n_flushed_lru;
			n_flushed_last += n_flushed_list;

			n_flushed = n_flushed_lru + n_flushed_list;

			if (n_flushed_lru) {
				MONITOR_INC_VALUE_CUMULATIVE(
					MONITOR_LRU_BATCH_FLUSH_TOTAL_PAGE,
					MONITOR_LRU_BATCH_FLUSH_COUNT,
					MONITOR_LRU_BATCH_FLUSH_PAGES,
					n_flushed_lru);
			}

			if (n_flushed_list) {
				MONITOR_INC_VALUE_CUMULATIVE(
					MONITOR_FLUSH_ADAPTIVE_TOTAL_PAGE,
					MONITOR_FLUSH_ADAPTIVE_COUNT,
					MONITOR_FLUSH_ADAPTIVE_PAGES,
					n_flushed_list);
			}

		/*  
			--------------------------------------------------------------------------------------------
			空闲刷新
			这时已经检查了没有其他活动在进行，也即是idle， 那么就进行批量flush操作。
		*/
		} else if (ret_sleep == OS_SYNC_TIME_EXCEEDED) {
			/* no activity, slept enough */
			/* 刷新srv_io_capacity个脏页到磁盘 */
			/* PCT_IO(100) = ((ulong) (srv_io_capacity * ((double) (100) / 100.0))) */
			buf_flush_lists(PCT_IO(100), LSN_MAX, &n_flushed);

			n_flushed_last += n_flushed;

			if (n_flushed) {
				MONITOR_INC_VALUE_CUMULATIVE(
					MONITOR_FLUSH_BACKGROUND_TOTAL_PAGE,
					MONITOR_FLUSH_BACKGROUND_COUNT,
					MONITOR_FLUSH_BACKGROUND_PAGES,
					n_flushed);

			}

		} else {
			/* no activity, but woken up by event */
			n_flushed = 0;
		}

		ut_d(buf_flush_page_cleaner_disabled_loop());
	}

	ut_ad(srv_shutdown_state > 0);
	if (srv_fast_shutdown == 2
	    || srv_shutdown_state == SRV_SHUTDOWN_EXIT_THREADS) {
		/* In very fast shutdown or when innodb failed to start, we
		simulate a crash of the buffer pool. We are not required to do
		any flushing. */
		goto thread_exit;
	}

	/* In case of normal and slow shutdown the page_cleaner thread
	must wait for all other activity in the server to die down.
	Note that we can start flushing the buffer pool as soon as the
	server enters shutdown phase but we must stay alive long enough
	to ensure that any work done by the master or purge threads is
	also flushed.
	During shutdown we pass through two stages. In the first stage,
	when SRV_SHUTDOWN_CLEANUP is set other threads like the master
	and the purge threads may be working as well. We start flushing
	the buffer pool but can't be sure that no new pages are being
	dirtied until we enter SRV_SHUTDOWN_FLUSH_PHASE phase. */
	/*
--------------------------------------------------------------------------------------------------------------
		InnoDB正常关闭情况下的处理	  
	*/
	do {
		pc_request(ULINT_MAX, LSN_MAX);

		while (pc_flush_slot() > 0) {}

		ulint	n_flushed_lru = 0;
		ulint	n_flushed_list = 0;
		pc_wait_finished(&n_flushed_lru, &n_flushed_list);

		n_flushed = n_flushed_lru + n_flushed_list;

		/* We sleep only if there are no pages to flush */
		if (n_flushed == 0) {
			os_thread_sleep(100000);
		}
	} while (srv_shutdown_state == SRV_SHUTDOWN_CLEANUP);

	/* At this point all threads including the master and the purge
	thread must have been suspended. */
	ut_a(srv_get_active_thread_type() == SRV_NONE);
	ut_a(srv_shutdown_state == SRV_SHUTDOWN_FLUSH_PHASE);

	/* We can now make a final sweep on flushing the buffer pool
	and exit after we have cleaned the whole buffer pool.
	It is important that we wait for any running batch that has
	been triggered by us to finish. Otherwise we can end up
	considering end of that batch as a finish of our final
	sweep and we'll come out of the loop leaving behind dirty pages
	in the flush_list */
	buf_flush_wait_batch_end(NULL, BUF_FLUSH_LIST);
	buf_flush_wait_LRU_batch_end();

	bool	success;

	do {
		pc_request(ULINT_MAX, LSN_MAX);

		while (pc_flush_slot() > 0) {}

		ulint	n_flushed_lru = 0;
		ulint	n_flushed_list = 0;
		success = pc_wait_finished(&n_flushed_lru, &n_flushed_list);

		n_flushed = n_flushed_lru + n_flushed_list;

		buf_flush_wait_batch_end(NULL, BUF_FLUSH_LIST);
		buf_flush_wait_LRU_batch_end();

	} while (!success || n_flushed > 0);

	/* Some sanity checks */
	ut_a(srv_get_active_thread_type() == SRV_NONE);
	ut_a(srv_shutdown_state == SRV_SHUTDOWN_FLUSH_PHASE);

	for (ulint i = 0; i < srv_buf_pool_instances; i++) {
		buf_pool_t* buf_pool = buf_pool_from_array(i);
		ut_a(UT_LIST_GET_LEN(buf_pool->flush_list) == 0);
	}

	/* We have lived our life. Time to die. */

thread_exit:
	/* All worker threads are waiting for the event here,
	and no more access to page_cleaner structure by them.
	Wakes worker threads up just to make them exit. */
	page_cleaner->is_running = false;
	os_event_set(page_cleaner->is_requested);

	buf_flush_page_cleaner_close();

	buf_page_cleaner_is_active = false;

	my_thread_end();

	/* We count the number of threads in os_thread_exit(). A created
	thread should always use that to exit and not use return() to exit. */
	os_thread_exit();

	OS_THREAD_DUMMY_RETURN;
}

/******************************************************************//**
Worker thread of page_cleaner.
@return a dummy parameter */
extern "C"
os_thread_ret_t
DECLARE_THREAD(buf_flush_page_cleaner_worker)(
/*==========================================*/
	void*	arg MY_ATTRIBUTE((unused)))
			/*!< in: a dummy parameter required by
			os_thread_create */
{
	my_thread_init();

	mutex_enter(&page_cleaner->mutex);
	page_cleaner->n_workers++;
	mutex_exit(&page_cleaner->mutex);

#ifdef UNIV_LINUX
	/* linux might be able to set different setting for each thread
	worth to try to set high priority for page cleaner threads */
	if (buf_flush_page_cleaner_set_priority(
		buf_flush_page_cleaner_priority)) {

		ib::info() << "page_cleaner worker priority: "
			<< buf_flush_page_cleaner_priority;
	}
#endif /* UNIV_LINUX */

	while (true) {
		/* 等待page_cleaner_coordinator设置page_cleaner->is_requested唤起worker线程 */
		os_event_wait(page_cleaner->is_requested);

		ut_d(buf_flush_page_cleaner_disabled_loop());

		if (!page_cleaner->is_running) {
			break;
		}

		pc_flush_slot();
	}

	mutex_enter(&page_cleaner->mutex);
	page_cleaner->n_workers--;
	mutex_exit(&page_cleaner->mutex);

	my_thread_end();

	os_thread_exit();

	OS_THREAD_DUMMY_RETURN;
}

/*******************************************************************//**
Synchronously flush dirty blocks from the end of the flush list of all buffer
pool instances.
NOTE: The calling thread is not allowed to own any latches on pages! */
void
buf_flush_sync_all_buf_pools(void)
/*==============================*/
{
	bool success;
	do {
		success = buf_flush_lists(ULINT_MAX, LSN_MAX, NULL);
		buf_flush_wait_batch_end(NULL, BUF_FLUSH_LIST);
	} while (!success);

	ut_a(success);
}

/** Request IO burst and wake page_cleaner up.
@param[in]	lsn_limit	upper limit of LSN to be flushed */
void
buf_flush_request_force(
	lsn_t	lsn_limit)
{
	/* adjust based on lsn_avg_rate not to get old */
	lsn_t	lsn_target = lsn_limit + lsn_avg_rate * 3;

	mutex_enter(&page_cleaner->mutex);
	if (lsn_target > buf_flush_sync_lsn) {
		buf_flush_sync_lsn = lsn_target;
	}
	mutex_exit(&page_cleaner->mutex);

	os_event_set(buf_flush_event);
}
#if defined UNIV_DEBUG || defined UNIV_BUF_DEBUG

/** Functor to validate the flush list. */
struct	Check {
	void	operator()(const buf_page_t* elem)
	{
		ut_a(elem->in_flush_list);
	}
};

/******************************************************************//**
Validates the flush list.
@return TRUE if ok */
static
ibool
buf_flush_validate_low(
/*===================*/
	buf_pool_t*	buf_pool)		/*!< in: Buffer pool instance */
{
	buf_page_t*		bpage;
	const ib_rbt_node_t*	rnode = NULL;
	Check			check;

	ut_ad(buf_flush_list_mutex_own(buf_pool));

	ut_list_validate(buf_pool->flush_list, check);

	bpage = UT_LIST_GET_FIRST(buf_pool->flush_list);

	/* If we are in recovery mode i.e.: flush_rbt != NULL
	then each block in the flush_list must also be present
	in the flush_rbt. */
	if (buf_pool->flush_rbt != NULL) {
		rnode = rbt_first(buf_pool->flush_rbt);
	}

	while (bpage != NULL) {
		const lsn_t	om = bpage->oldest_modification;

		ut_ad(buf_pool_from_bpage(bpage) == buf_pool);

		ut_ad(bpage->in_flush_list);

		/* A page in buf_pool->flush_list can be in
		BUF_BLOCK_REMOVE_HASH state. This happens when a page
		is in the middle of being relocated. In that case the
		original descriptor can have this state and still be
		in the flush list waiting to acquire the
		buf_pool->flush_list_mutex to complete the relocation. */
		ut_a(buf_page_in_file(bpage)
		     || buf_page_get_state(bpage) == BUF_BLOCK_REMOVE_HASH);
		ut_a(om > 0);

		if (buf_pool->flush_rbt != NULL) {
			buf_page_t**	prpage;

			ut_a(rnode != NULL);
			prpage = rbt_value(buf_page_t*, rnode);

			ut_a(*prpage != NULL);
			ut_a(*prpage == bpage);
			rnode = rbt_next(buf_pool->flush_rbt, rnode);
		}

		bpage = UT_LIST_GET_NEXT(list, bpage);

		ut_a(bpage == NULL || om >= bpage->oldest_modification);
	}

	/* By this time we must have exhausted the traversal of
	flush_rbt (if active) as well. */
	ut_a(rnode == NULL);

	return(TRUE);
}

/******************************************************************//**
Validates the flush list.
@return TRUE if ok */
ibool
buf_flush_validate(
/*===============*/
	buf_pool_t*	buf_pool)	/*!< buffer pool instance */
{
	ibool	ret;

	buf_flush_list_mutex_enter(buf_pool);

	ret = buf_flush_validate_low(buf_pool);

	buf_flush_list_mutex_exit(buf_pool);

	return(ret);
}
#endif /* UNIV_DEBUG || UNIV_BUF_DEBUG */
#endif /* !UNIV_HOTBACKUP */

/******************************************************************//**
Check if there are any dirty pages that belong to a space id in the flush
list in a particular buffer pool.
@return number of dirty pages present in a single buffer pool */
ulint
buf_pool_get_dirty_pages_count(
/*===========================*/
	buf_pool_t*	buf_pool,	/*!< in: buffer pool */
	ulint		id,		/*!< in: space id to check */
	FlushObserver*	observer)	/*!< in: flush observer to check */

{
	ulint		count = 0;

	buf_pool_mutex_enter(buf_pool);
	buf_flush_list_mutex_enter(buf_pool);

	buf_page_t*	bpage;

	for (bpage = UT_LIST_GET_FIRST(buf_pool->flush_list);
	     bpage != 0;
	     bpage = UT_LIST_GET_NEXT(list, bpage)) {

		ut_ad(buf_page_in_file(bpage));
		ut_ad(bpage->in_flush_list);
		ut_ad(bpage->oldest_modification > 0);

		if ((observer != NULL
		     && observer == bpage->flush_observer)
		    || (observer == NULL
			&& id == bpage->id.space())) {
			++count;
		}
	}

	buf_flush_list_mutex_exit(buf_pool);
	buf_pool_mutex_exit(buf_pool);

	return(count);
}

/******************************************************************//**
Check if there are any dirty pages that belong to a space id in the flush list.
@return number of dirty pages present in all the buffer pools */
ulint
buf_flush_get_dirty_pages_count(
/*============================*/
	ulint		id,		/*!< in: space id to check */
	FlushObserver*	observer)	/*!< in: flush observer to check */
{
	ulint		count = 0;

	for (ulint i = 0; i < srv_buf_pool_instances; ++i) {
		buf_pool_t*	buf_pool;

		buf_pool = buf_pool_from_array(i);

		count += buf_pool_get_dirty_pages_count(buf_pool, id, observer);
	}

	return(count);
}

/** FlushObserver constructor
@param[in]	space_id	table space id
@param[in]	trx		trx instance
@param[in]	stage		performance schema accounting object,
used by ALTER TABLE. It is passed to log_preflush_pool_modified_pages()
for accounting. */
FlushObserver::FlushObserver(
	ulint			space_id,
	trx_t*			trx,
	ut_stage_alter_t*	stage)
	:
	m_space_id(space_id),
	m_trx(trx),
	m_stage(stage),
	m_interrupted(false)
{
	m_flushed = UT_NEW_NOKEY(std::vector<ulint>(srv_buf_pool_instances));
	m_removed = UT_NEW_NOKEY(std::vector<ulint>(srv_buf_pool_instances));

	for (ulint i = 0; i < srv_buf_pool_instances; i++) {
		m_flushed->at(i) = 0;
		m_removed->at(i) = 0;
	}

#ifdef FLUSH_LIST_OBSERVER_DEBUG
		ib::info() << "FlushObserver constructor: " << m_trx->id;
#endif /* FLUSH_LIST_OBSERVER_DEBUG */
}

/** FlushObserver deconstructor */
FlushObserver::~FlushObserver()
{
	ut_ad(buf_flush_get_dirty_pages_count(m_space_id, this) == 0);

	UT_DELETE(m_flushed);
	UT_DELETE(m_removed);

#ifdef FLUSH_LIST_OBSERVER_DEBUG
		ib::info() << "FlushObserver deconstructor: " << m_trx->id;
#endif /* FLUSH_LIST_OBSERVER_DEBUG */
}

/** Check whether trx is interrupted
@return true if trx is interrupted */
bool
FlushObserver::check_interrupted()
{
	if (trx_is_interrupted(m_trx)) {
		interrupted();

		return(true);
	}

	return(false);
}

/** Notify observer of a flush
@param[in]	buf_pool	buffer pool instance
@param[in]	bpage		buffer page to flush */
void
FlushObserver::notify_flush(
	buf_pool_t*	buf_pool,
	buf_page_t*	bpage)
{
	ut_ad(buf_pool_mutex_own(buf_pool));

	m_flushed->at(buf_pool->instance_no)++;

	if (m_stage != NULL) {
		m_stage->inc();
	}

#ifdef FLUSH_LIST_OBSERVER_DEBUG
	ib::info() << "Flush <" << bpage->id.space()
		   << ", " << bpage->id.page_no() << ">";
#endif /* FLUSH_LIST_OBSERVER_DEBUG */
}

/** Notify observer of a remove
@param[in]	buf_pool	buffer pool instance
@param[in]	bpage		buffer page flushed */
void
FlushObserver::notify_remove(
	buf_pool_t*	buf_pool,
	buf_page_t*	bpage)
{
	ut_ad(buf_pool_mutex_own(buf_pool));

	m_removed->at(buf_pool->instance_no)++;

#ifdef FLUSH_LIST_OBSERVER_DEBUG
	ib::info() << "Remove <" << bpage->id.space()
		   << ", " << bpage->id.page_no() << ">";
#endif /* FLUSH_LIST_OBSERVER_DEBUG */
}

/** Flush dirty pages and wait. */
void
FlushObserver::flush()
{
	buf_remove_t	buf_remove;

	if (m_interrupted) {
		buf_remove = BUF_REMOVE_FLUSH_NO_WRITE;
	} else {
		buf_remove = BUF_REMOVE_FLUSH_WRITE;

		if (m_stage != NULL) {
			ulint	pages_to_flush =
				buf_flush_get_dirty_pages_count(
					m_space_id, this);

			m_stage->begin_phase_flush(pages_to_flush);
		}
	}

	/* Flush or remove dirty pages. */
	buf_LRU_flush_or_remove_pages(m_space_id, buf_remove, m_trx);

	/* Wait for all dirty pages were flushed. */
	for (ulint i = 0; i < srv_buf_pool_instances; i++) {
		while (!is_complete(i)) {

			os_thread_sleep(2000);
		}
	}
}
