/*	$OpenBSD: btree.c,v 1.30 2010/09/01 12:13:21 martinh Exp $ */

/*
 * Copyright (c) 2009, 2010 Martin Hedenfalk <martin@bzero.se>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */
#define _POSIX_C_SOURCE 199309L
#include <sys/types.h>
#include "./sys/tree.h"
#include <sys/stat.h>
#include <sys/queue.h>
#include <sys/param.h>
#include <sys/uio.h>

#include <sys/file.h>

#include <assert.h>
#include <err.h>
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <stdbool.h>

#include "btree.h"

/* from compat.h */
#ifndef __packed
#define __packed __attribute__ ((__packed__))
#endif

/* #define DEBUG */

#ifdef DEBUG
# define DPRINTF(...)	do { fprintf(stderr, "%s:%d: ", __func__, __LINE__); \
			     fprintf(stderr, __VA_ARGS__); \
			     fprintf(stderr, "\n"); } while(0)
#else
# define DPRINTF(...)	do { } while(0)
#endif

#define PAGESIZE	 4096
#define BT_MINKEYS	 4
#define BT_MAGIC	 0xB3DBB3DB
#define BT_VERSION	 4
#define MAXKEYSIZE	 255

#define P_INVALID	 0xFFFFFFFF

#define F_ISSET(w, f)	 (((w) & (f)) == (f))

typedef uint32_t	 pgno_t;//4k* 4G
typedef uint16_t	 indx_t;

/* There are four page types: meta, index, leaf and overflow.
 * They all share the same page header.
 */
#define	P_BRANCH	 0x01		/* branch page */
#define	P_LEAF		 0x02		/* leaf page */
#define	P_OVERFLOW	 0x04		/* overflow page */
#define	P_META		 0x08		/* meta page */
#define	P_HEAD		 0x10		/* header page */
#define lower		 b.fb.fb_lower
#define upper		 b.fb.fb_upper
#define p_next_pgno	 b.pb_next_pgno
struct page {				/* represents an on-disk page */
	pgno_t		 pgno;		/* page number */
	uint32_t	 flags;
//layout
	union page_bounds {
		struct {
			indx_t	 fb_lower;	/* lower bound of free space */
			indx_t	 fb_upper;	/* upper bound of free space */
		} fb;
		pgno_t		 pb_next_pgno;	/* overflow page linked list */
	} b;
	indx_t		 offsets[1];		/* dynamic size */
} __attribute__ ((__packed__));

#define PAGEHDRSZ	 offsetof(struct page, offsets)

#define NUMKEYSP(p)	 (((p)->lower - PAGEHDRSZ) >> 1)
#define NUMKEYS(mp)	 (((mp)->page->lower - PAGEHDRSZ) >> 1)
#define SIZELEFT(mp)	 (indx_t)((mp)->page->upper - (mp)->page->lower)
#define PAGEFILL(bt, mp) (1000 * ((bt)->head.psize - PAGEHDRSZ - SIZELEFT(mp)) / \
				((bt)->head.psize - PAGEHDRSZ))
#define IS_LEAF(mp)	 F_ISSET((mp)->page->flags, P_LEAF)
#define IS_BRANCH(mp)	 F_ISSET((mp)->page->flags, P_BRANCH)
#define IS_OVERFLOW(mp)	 F_ISSET((mp)->page->flags, P_OVERFLOW)

struct bt_head {				/* header page content */
	uint32_t	 magic;
	uint32_t	 version;
	uint32_t	 flags;
	uint32_t	 psize;			/* page size */
} __attribute__ ((__packed__));
#define BT_TOMBSTONE	 0x01			/* file is replaced */
struct bt_meta {				/* meta (footer) page content */

	uint32_t	 flags;
	pgno_t		 root;			/* page number of root page */
	pgno_t		 prev_meta;		/* previous meta page number */
	time_t		 created_at;
	uint32_t	 branch_pages;
	uint32_t	 leaf_pages;
	uint32_t	 overflow_pages;
	uint32_t	 revisions;
	uint32_t	 depth;
	uint64_t	 entries;
	unsigned char	 hash[SHA1_DIGEST_LENGTH];
} __attribute__ ((__packed__));

struct btkey {
	size_t			 len;
	char			 str[MAXKEYSIZE];
};

struct mpage {					/* an in-memory cached page */
	RB_ENTRY(mpage)		 entry;		/* page cache entry */
	//SIMPLEQ_ENTRY(mpage)	 next;		/* queue of dirty pages */
	struct{
		struct mpage *sqe_next;	/* next element */		
	}next;	
	TAILQ_ENTRY(mpage)	 lru_next;	/* LRU queue */
	struct mpage		*parent;	/* NULL if root */
	unsigned int		 parent_index;	/* keep track of node index */
	struct page		*page;
	pgno_t			 pgno;		/* copy of page->pgno */
	short			 ref;		/* increased by cursors */
	short			 dirty;		/* 1 if on dirty queue */
};
RB_HEAD(page_cache, mpage);
//SIMPLEQ_HEAD(dirty_queue, mpage);
struct dirty_queue {								
	struct mpage *sqh_first;	/* first element */			
	struct mpage **sqh_last;	/* addr of last next element */		
};

TAILQ_HEAD(lru_queue, mpage);

static int		 mpage_cmp(struct mpage *a, struct mpage *b);
static struct mpage	*mpage_lookup(struct btree *bt, pgno_t pgno);
static void		 mpage_add(struct btree *bt, struct mpage *mp);
static void		 mpage_free(struct mpage *mp);
static void		 mpage_del(struct btree *bt, struct mpage *mp);
static void		 mpage_flush(struct btree *bt);
static struct mpage	*mpage_copy(struct btree *bt, struct mpage *mp);
static void		 mpage_prune(struct btree *bt);
static void		 mpage_dirty(struct btree_txn *txn, struct mpage *mp);
static struct mpage	*mpage_copy_on_write(struct btree *bt, struct mpage *mp);

RB_PROTOTYPE(page_cache, mpage, entry, mpage_cmp);
RB_GENERATE(page_cache, mpage, entry, mpage_cmp);

struct ppage {					/* ordered list of pages */
	//SLIST_ENTRY(ppage)	 entry;
	struct {								
		struct ppage *sle_next;	/* next element */			
	}entry;
	struct mpage		*mpage;
	unsigned int		 ki;		/* cursor index on page */
};
//SLIST_HEAD(page_stack, ppage);
struct page_stack {								
	struct ppage *slh_first;	/* first element */			
};

#define CURSOR_EMPTY(c)		 SLIST_EMPTY(&(c)->stack)
#define CURSOR_TOP(c)		 SLIST_FIRST(&(c)->stack)
#define CURSOR_POP(c)		 SLIST_REMOVE_HEAD(&(c)->stack, entry)
#define CURSOR_PUSH(c,p)	 SLIST_INSERT_HEAD(&(c)->stack, p, entry)

struct cursor {
	struct btree		*bt;
	struct btree_txn	*txn;
	struct page_stack	 stack;		/* stack of parent pages */
	short			 initialized;	/* 1 if initialized */
	short			 eof;		/* 1 if end is reached */
};

#define METAHASHLEN	 offsetof(struct bt_meta, hash)
#define METADATA(p)	 ((void *)((char *)p + PAGEHDRSZ))

#define n_pgno		 p.np_pgno
#define n_dsize		 p.np_dsize
#define F_BIGDATA	 0x01			/* data put on overflow page */
struct node {
	union {
		pgno_t		 np_pgno;	/* child page number */
		uint32_t	 np_dsize;	/* leaf data size */
	}		 p;
	uint16_t	 ksize;			/* key size */
	uint8_t		 flags;
	char		 data[1];
} __packed;

struct btree_txn {
	pgno_t			 root;		/* current / new root page */
	pgno_t			 next_pgno;	/* next unallocated page */
	struct btree		*bt;		/* btree is ref'd */
	struct dirty_queue	*dirty_queue;	/* modified pages */
#define BT_TXN_RDONLY		 0x01		/* read-only transaction */
#define BT_TXN_ERROR		 0x02		/* an error has occurred */
	unsigned int		 flags;
};
#define BT_FIXPADDING		 0x01		/* internal */
struct btree {
	int			 			fd;
	char			*		path;

	unsigned int		 flags;
	bt_cmp_func		 	 cmp;		/* user compare function */
	struct bt_head		 head;
	struct bt_meta		 meta;
	struct page_cache	*page_cache;
	struct lru_queue	*lru_queue;
	struct btree_txn	*txn;		/* current write transaction */
	int			 		ref;		/* increased by cursors & txn */
	struct btree_stat	stat;
	off_t			 	size;		/* current file size */
	pgno_t				meta_pgno;
};

#define NODESIZE	 offsetof(struct node, data)

#define INDXSIZE(k)	 (NODESIZE + ((k) == NULL ? 0 : (k)->size))
#define LEAFSIZE(k, d)	 (NODESIZE + (k)->size + (d)->size)
#define NODEPTRP(p, i)	 ((struct node *)((char *)(p) + (p)->offsets[i]))
#define NODEPTR(mp, i)	 NODEPTRP((mp)->page, i)
#define NODEKEY(node)	 (void *)((node)->data)
#define NODEDATA(node)	 (void *)((char *)(node)->data + (node)->ksize)
#define NODEPGNO(node)	 ((node)->p.np_pgno)
#define NODEDSZ(node)	 ((node)->p.np_dsize)

#define BT_COMMIT_PAGES	 64	/* max number of pages to write in one commit */
#define BT_MAXCACHE_DEF	 1024	/* max number of pages to keep in cache  */

static int		 __btree_read_page(struct btree *bt, pgno_t pgno,
			    struct page *page);
static struct mpage	*btree_get_mpage(struct btree *bt, pgno_t pgno);
static int		 btree_search_leaf_page_from_root(struct btree *bt,
			    struct mpage *root, struct btval *key,
			    struct cursor *cursor, int modify,
			    struct mpage **mpp);
static int		 btree_search_leaf_page(struct btree *bt,
			    struct btree_txn *txn, struct btval *key,
			    struct cursor *cursor, int modify,
			    struct mpage **mpp);

static int		 btree_write_header(struct btree *bt, int fd);
static int		 btree_read_header(struct btree *bt);
static int		 btree_is_meta_page(struct page *p);
static int		 btree_read_meta(struct btree *bt, pgno_t *p_next);
static int		 btree_write_meta(struct btree *bt, pgno_t root,unsigned int flags);
static void		 btree_ref(struct btree *bt);

static struct node	*btree_search_in_leaf_page(struct btree *bt, struct mpage *mp,
			    struct btval *key, int *exactp, unsigned int *kip);
static int		 btree_insert_node(struct btree *bt, struct mpage *mp,
			    indx_t indx, const struct btval *key, struct btval *data,
			    pgno_t pgno, uint8_t flags);
static void		 __btree_del_node(struct mpage *mp,indx_t indx);
static int		 btree_read_data(struct btree *bt, struct mpage *mp,
			    struct node *leaf, struct btval *data);

static int		 btree_rebalance(struct btree *bt, struct mpage *mp);
static int		 btree_update_key(struct mpage *mp,
			    indx_t indx, struct btval *key);
static int		 btree_move_node(struct btree *bt, struct mpage *src_page, struct mpage *dst_page, bool is_tail);
static int		 btree_merge(struct btree *bt, const struct mpage *src, struct mpage *dst);
static int		 btree_split_insert(struct btree *bt, struct mpage **mpp,
			    unsigned int *newindxp, const struct btval *newkey,
			    const struct btval *newdata, pgno_t newpgno);
static struct mpage	*btree_new_page(struct btree *bt, uint32_t flags);
static int		 btree_write_overflow_data(struct btree *bt,
			    struct page *p, struct btval *data);

static void		 cursor_pop_page(struct cursor *cursor);
static struct ppage	 *cursor_push_page(struct cursor *cursor,
			    struct mpage *mp);

static int		 bt_set_key(struct btree *bt, struct mpage *mp,
			    struct node *node, struct btval *key);
static int		 btree_sibling(struct cursor *cursor, int move_right);
static int		 btree_cursor_next(struct cursor *cursor,
			    struct btval *key, struct btval *data);
static int		 btree_cursor_set(struct cursor *cursor,
			    struct btval *key, struct btval *data, int *exactp);
static int		 btree_cursor_first(struct cursor *cursor,
			    struct btval *key, struct btval *data);

static void		 bt_reduce_separator(struct btree *bt, struct node *min,
			    struct btval *sep);

static size_t		 bt_leaf_size(struct btree *bt, struct btval *key,struct btval *data);
static size_t		 bt_branch_size(struct btree *bt, struct btval *key);

static pgno_t		 btree_compact_tree(struct btree *bt, pgno_t pgno,
			    struct btree *btc);

static int		 memncmp(const void *s1, size_t n1,
				 const void *s2, size_t n2);
static int		 memnrcmp(const void *s1, size_t n1,
				  const void *s2, size_t n2);

static int
memncmp(const void *s1, size_t n1, const void *s2, size_t n2)
{
	if (n1 < n2) {
		if (memcmp(s1, s2, n1) == 0)
			return -1;
	}
	else if (n1 > n2) {
		if (memcmp(s1, s2, n2) == 0)
			return 1;
	}
	return memcmp(s1, s2, n1);
}

static int
memnrcmp(const void *s1, size_t n1, const void *s2, size_t n2)
{
	const unsigned char	*p1;
	const unsigned char	*p2;

	if (n1 == 0)
		return n2 == 0 ? 0 : -1;

	if (n2 == 0)
		return n1 == 0 ? 0 : 1;

	p1 = (const unsigned char *)s1 + n1 - 1;
	p2 = (const unsigned char *)s2 + n2 - 1;

	while (*p1 == *p2) {
		if (p1 == s1)
			return (p2 == s2) ? 0 : -1;
		if (p2 == s2)
			return (p1 == p2) ? 0 : 1;
		p1--;
		p2--;
	}
	return *p1 - *p2;
}

int
btree_cmp(struct btree *bt, const struct btval *a, const struct btval *b)
{
	if (bt->cmp)
			return bt->cmp(a,b);
		else{
				if (F_ISSET(bt->flags, BT_REVERSEKEY))
					return memnrcmp(a->data, a->size,b->data, b->size);
				else
					return memncmp(a->data, a->size,b->data, b->size);
			}

}

static int bt_cmp(struct btree *bt, const struct btval *key1, const struct btval *key2)
{
	if (F_ISSET(bt->flags, BT_REVERSEKEY))
		return memnrcmp(key1->data, key1->size,key2->data, key2->size);
	else
		return memncmp((char *)key1->data, key1->size ,key2->data, key2->size);
}

void btval_reset(struct btval *btv)
{
	if (btv) {
		if (btv->mp)
			btv->mp->ref--;
		if (btv->free_data)
			free(btv->data);
		memset(btv, 0, sizeof(*btv));
	}
}

static int mpage_cmp(struct mpage *a, struct mpage *b)
{
	if (a->pgno > b->pgno)
		return 1;
	if (a->pgno < b->pgno)
		return -1;
	return 0;
}

static struct mpage * mpage_lookup(struct btree *bt, pgno_t pgno)
{
	struct mpage	 find, *mp;

	find.pgno = pgno;
	mp = RB_FIND(page_cache, bt->page_cache, &find);
	if (mp) {
		bt->stat.hits++;
		/* Update LRU queue. Move page to the end. */
		TAILQ_REMOVE(bt->lru_queue, mp, lru_next);
		TAILQ_INSERT_TAIL(bt->lru_queue, mp, lru_next);
	}else{
		bt->stat.misses++;
	}
	return mp;
}

static void mpage_add(struct btree *bt, struct mpage *mp)
{
	assert(RB_INSERT(page_cache, bt->page_cache, mp) == NULL);
	bt->stat.cache_size++;
	TAILQ_INSERT_TAIL(bt->lru_queue, mp, lru_next);
}

static void mpage_free(struct mpage *mp)
{
	//DPRINTF("free page %u",mp->pgno);
	if (mp != NULL) {
		free(mp->page);
		free(mp);
	}
}

static void mpage_del(struct btree *bt, struct mpage *mp)
{
	assert(RB_REMOVE(page_cache, bt->page_cache, mp) == mp);
	assert(bt->stat.cache_size > 0);
	bt->stat.cache_size--;
	TAILQ_REMOVE(bt->lru_queue, mp, lru_next);
}

static void mpage_flush(struct btree *bt)
{
	struct mpage	*mp;

	while ((mp = RB_MIN(page_cache, bt->page_cache)) != NULL) {
		mpage_del(bt, mp);
		mpage_free(mp);
	}
}

static struct mpage * mpage_copy(struct btree *bt, struct mpage *mp)
{
	struct mpage	*copy;

	if ((copy = calloc(1, sizeof(*copy))) == NULL)
		return NULL;
	if ((copy->page = malloc(bt->head.psize)) == NULL) {
		free(copy);
		return NULL;
	}
	memcpy(copy->page, mp->page, bt->head.psize);
	
	copy->parent = mp->parent;
	copy->parent_index = mp->parent_index;
	copy->pgno = mp->pgno;

	return copy;
}

/* Remove the least recently used memory pages until the cache size is
 * within the configured bounds. Pages referenced by cursors or returned
 * key/data are not pruned.
 */
static void mpage_prune(struct btree *bt)
{
	struct mpage	*mp, *next;

	for (mp = TAILQ_FIRST(bt->lru_queue); mp; mp = next) {
		if (bt->stat.cache_size <= bt->stat.max_cache)//4k*1k 4m
			break;
		next = TAILQ_NEXT(mp, lru_next);
		if (!mp->dirty && mp->ref <= 0) {
			mpage_del(bt, mp);
			mpage_free(mp);
		}
	}
}

/* Mark a page as dirty and push it on the dirty queue.
 */
static void mpage_dirty(struct btree_txn* txn, struct mpage *mp)
{
	assert(txn->bt != NULL);
	assert(txn != NULL);

	if (!mp->dirty) {
		mp->dirty = 1;
		//SIMPLEQ_INSERT_TAIL(bt->txn->dirty_queue, mp, next);
		struct dirty_queue * head = txn->dirty_queue;
		mp->next.sqe_next = NULL;					
		*(head)->sqh_last = mp;					
		(head)->sqh_last = &mp->next.sqe_next;			
	}
}

/* Touch a page: make it dirty and re-insert into tree with updated pgno.
 */
static struct mpage * mpage_copy_on_write(struct btree *bt, struct mpage *mp)
{
	assert(bt != NULL);
	assert(bt->txn != NULL);
	assert(mp != NULL);

	if (!mp->dirty) {
		DPRINTF("touching page %u -> %u mp->ref=%d", mp->pgno, bt->txn->next_pgno, mp->ref);
		if (mp->ref == 0)
			mpage_del(bt, mp);
		else {
			if ((mp = mpage_copy(bt, mp)) == NULL)
				return NULL;
		}
		mp->pgno = mp->page->pgno = bt->txn->next_pgno++;
		mpage_dirty(bt->txn, mp);
		mpage_add(bt, mp);

		/* Update the page number to new touched page. */
		if (mp->parent != NULL){
				assert(mp->parent->dirty==1);
				assert( (mp->parent->page->flags&P_BRANCH)!=0);
				struct node * p_node= (struct node*)((char*)mp->parent->page+ mp->parent->page->offsets[mp->parent_index]);
				p_node->p.np_pgno=mp->pgno;
				//NODEPGNO(NODEPTR(mp->parent,mp->parent_index)) = mp->pgno;
			}
	}

	return mp;
}

static int __btree_read_page(struct btree *bt, pgno_t pgno, struct page *page)
{
	ssize_t		 rc;

	DPRINTF("reading page %u", pgno);
	bt->stat.reads++;
	if ((rc = pread(bt->fd, page, bt->head.psize, (off_t)pgno*bt->head.psize)) == 0) {
		DPRINTF("page %u doesn't exist", pgno);
		errno = ENOENT;
		return BT_FAIL;
	} else if (rc != (ssize_t)bt->head.psize) {
		if (rc > 0)
			errno = EINVAL;
		DPRINTF("read: %s", strerror(errno));
		return BT_FAIL;
	}

	if (page->pgno != pgno) {
		DPRINTF("page numbers don't match: %u != %u", pgno, page->pgno);
		errno = EINVAL;
		return BT_FAIL;
	}
	const char * tag= page->flags == P_BRANCH? "branch" : 
	page->flags==P_LEAF ? "leaf" : ( page->flags == P_META  ? "meta": "other");
	DPRINTF("page %u has flags %s 0x%X", pgno,tag,page->flags);

	return BT_SUCCESS;
}

int btree_sync(struct btree *bt)
{
	if (!F_ISSET(bt->flags, BT_NOSYNC)){
		bt->stat.fsyncs++;
		return fdatasync(bt->fd);
	}
	
	return 0;
}

struct btree_txn * btree_txn_begin(struct btree *bt, int rdonly)
{
	struct btree_txn	*txn;

	if (!rdonly && bt->txn != NULL) {
		DPRINTF("write transaction already begun");
		errno = EBUSY;
		return NULL;
	}

	if ((txn = calloc(1, sizeof(*txn))) == NULL) {
		DPRINTF("calloc: %s", strerror(errno));
		return NULL;
	}

	if (rdonly) {
		txn->flags |= BT_TXN_RDONLY;
	} else {
		txn->dirty_queue = calloc(1, sizeof(*txn->dirty_queue));
		if (txn->dirty_queue == NULL) {
			free(txn);
			return NULL;
		}
		//SIMPLEQ_INIT(txn->dirty_queue);
		{
				txn->dirty_queue->sqh_first = NULL;					
				txn->dirty_queue->sqh_last = &txn->dirty_queue->sqh_first;				
		}

		DPRINTF("taking write lock on txn %p", txn);
		if (flock(bt->fd, LOCK_EX | LOCK_NB) != 0) {
			DPRINTF("flock: %s", strerror(errno));
			errno = EBUSY;
			free(txn->dirty_queue);
			free(txn);
			return NULL;
		}
		bt->txn = txn;
	}

	txn->bt = bt;
	btree_ref(bt);

	if (btree_read_meta(bt, &txn->next_pgno) != BT_SUCCESS) {
		btree_txn_abort(txn);
		return NULL;
	}

	txn->root = bt->meta.root;
	DPRINTF("begin transaction on btree %p, root page %u", bt, txn->root);

	return txn;
}

void btree_txn_abort(struct btree_txn *txn)
{
	struct mpage	*mp;
	struct btree	*bt;

	if (txn == NULL)
		return;

	bt = txn->bt;
	DPRINTF("abort transaction on btree %p, root page %u", bt, txn->root);

	if (!F_ISSET(txn->flags, BT_TXN_RDONLY)) {
		/* Discard all dirty pages.
		 */
		while (!SIMPLEQ_EMPTY(txn->dirty_queue)) {
			mp = SIMPLEQ_FIRST(txn->dirty_queue);
			assert(mp->ref == 0);	/* cursors should be closed */
			mpage_del(bt, mp);
			SIMPLEQ_REMOVE_HEAD(txn->dirty_queue, next);
			mpage_free(mp);
		}

		DPRINTF("releasing write lock on txn %p", txn);
		txn->bt->txn = NULL;
		if (flock(txn->bt->fd, LOCK_UN) != 0) {
			DPRINTF("failed to unlock fd %d: %s",
			    txn->bt->fd, strerror(errno));
		}
		free(txn->dirty_queue);
	}

	btree_close(txn->bt);
	free(txn);
}

int btree_txn_commit(struct btree_txn *txn)
{
	int		 n, done;
	ssize_t		 rc;
	off_t		 size;
	struct mpage	*mp;

	struct iovec	 iov[BT_COMMIT_PAGES];

	assert(txn != NULL);
	assert(txn->bt != NULL);

	struct btree	*const bt = txn->bt;

	if (F_ISSET(txn->flags, BT_TXN_RDONLY)) {
		DPRINTF("attempt to commit read-only transaction");
		btree_txn_abort(txn);
		errno = EPERM;
		return BT_FAIL;
	}

	if (txn != bt->txn) {
		DPRINTF("attempt to commit unknown transaction");
		btree_txn_abort(txn);
		errno = EINVAL;
		return BT_FAIL;
	}

	if (F_ISSET(txn->flags, BT_TXN_ERROR)) {
		DPRINTF("error flag is set, can't commit");
		btree_txn_abort(txn);
		errno = EINVAL;
		return BT_FAIL;
	}

	if (SIMPLEQ_EMPTY(txn->dirty_queue))
		goto done;

	if (F_ISSET(bt->flags, BT_FIXPADDING)) {
		size = lseek(bt->fd, 0, SEEK_END);
		size += bt->head.psize - (size % bt->head.psize);
		DPRINTF("extending to multiple of page size: %lu", size);
		if (ftruncate(bt->fd, size) != 0) {
			DPRINTF("ftruncate: %s", strerror(errno));
			btree_txn_abort(txn);
			return BT_FAIL;
		}
		bt->flags &= ~BT_FIXPADDING;
	}

	DPRINTF("committing transaction on btree %p, root page %u",bt, txn->root);

	/* Commit up to BT_COMMIT_PAGES dirty pages to disk until done.
	 */
	do {
		n = 0;
		done = 1;
		SIMPLEQ_FOREACH(mp, txn->dirty_queue, next) {
			DPRINTF("commiting page %u", mp->pgno);
			iov[n].iov_len = bt->head.psize;
			iov[n].iov_base = mp->page;
			if (++n >= BT_COMMIT_PAGES) {
				done = 0;
				break;
			}
		}

		if (n == 0)
			break;

		
		rc = writev(bt->fd, iov, n);
		printf("commiting %u dirty pages\n", n);
		bt->stat.writes+=n;
		if (rc != (ssize_t)bt->head.psize*n) {
			if (rc > 0)
				DPRINTF("short write, filesystem full?");
			else
				DPRINTF("writev: %s", strerror(errno));
			btree_txn_abort(txn);
			return BT_FAIL;
		}

		/* Remove the dirty flag from the written pages.
		 */
		while (!SIMPLEQ_EMPTY(txn->dirty_queue)) {
			mp = SIMPLEQ_FIRST(txn->dirty_queue);
			mp->dirty = 0;
			SIMPLEQ_REMOVE_HEAD(txn->dirty_queue, next);
			if (--n == 0)
				break;
		}
	} while (!done);

	if (btree_sync(bt) != 0 ||
	    btree_write_meta(bt, txn->root,0) != BT_SUCCESS ||
	    btree_sync(bt) != 0) {
		btree_txn_abort(txn);
		return BT_FAIL;
	}

done:
	mpage_prune(bt);
	btree_txn_abort(txn);

	return BT_SUCCESS;
}

static int btree_write_header(struct btree *bt, int fd)
{
	struct stat	 sb;
	struct bt_head	*h;
	struct page	*p;
	ssize_t		 rc;
	unsigned int	 psize;

	DPRINTF("writing header page");
	assert(bt != NULL);

	/* Ask stat for 'optimal blocksize for I/O'.
	 */
	if (fstat(fd, &sb) == 0)
		psize = sb.st_blksize;
	else
		psize = PAGESIZE;

	if ((p = calloc(1, psize)) == NULL)
		return -1;
	p->flags = P_HEAD;

	h = METADATA(p);
	h->magic = BT_MAGIC;
	h->version = BT_VERSION;
	h->psize = psize;
	memcpy(&bt->head, h, sizeof(*h));

	rc = write(fd, p, bt->head.psize);
	free(p);
	if (rc != (ssize_t)bt->head.psize) {
		if (rc > 0)
			DPRINTF("short write, filesystem full?");
		return BT_FAIL;
	}

	return BT_SUCCESS;
}

static int btree_read_header(struct btree *bt)
{
	char page[PAGESIZE];
	struct page	*p;
	struct bt_head	*h;
	int		 rc;

	assert(bt != NULL);

	/* We don't know the page size yet, so use a minimum value.
	 */

	if ((rc = pread(bt->fd, page, PAGESIZE, 0)) == 0) {
		errno = ENOENT;
		return -1;
	} else if (rc != PAGESIZE) {
		if (rc > 0)
			errno = EINVAL;
		DPRINTF("read: %s", strerror(errno));
		return -1;
	}

	p = (struct page *)page;

	if (!F_ISSET(p->flags, P_HEAD)) {
		DPRINTF("page %d not a header page", p->pgno);
		errno = EINVAL;
		return -1;
	}

	h = METADATA(p);
	if (h->magic != BT_MAGIC) {
		DPRINTF("header has invalid magic");
		errno = EINVAL;
		return -1;
	}

	if (h->version != BT_VERSION) {
		DPRINTF("database is version %u, expected version %u",
		    bt->head.version, BT_VERSION);
		errno = EINVAL;
		return -1;
	}

	memcpy(&bt->head, h, sizeof(*h));
	return 0;
}

static int btree_write_meta(struct btree *bt, pgno_t root, unsigned int flags)
{
	struct mpage	*mp;
	
	ssize_t		 rc;
	DPRINTF("writing meta page for root page %u %u", root, flags);

	assert(bt != NULL);
	assert(bt->txn != NULL);
	//assert(bt->meta.root == P_INVALID || root>=bt->meta.root);
	assert(bt->txn->dirty_queue->sqh_first==NULL);
	if ((mp = btree_new_page(bt, P_META)) == NULL)
		return -1;
	bt->meta.prev_meta = bt->meta_pgno;
	bt->meta.root = root;
	bt->meta.flags = flags;
	bt->meta.created_at = time(0);
	bt->meta.revisions++;
	sha1((unsigned char *)&bt->meta, METAHASHLEN, bt->meta.hash);

	/* Copy the meta data changes to the new meta page. */
	struct bt_meta	*meta = METADATA(mp->page);
	memcpy(meta, &bt->meta, sizeof(*meta));

	rc = write(bt->fd, mp->page, bt->head.psize);
	mp->dirty = 0;

	SIMPLEQ_REMOVE_HEAD(bt->txn->dirty_queue, next);
	if (rc != (ssize_t)bt->head.psize) {
		if (rc > 0)
			DPRINTF("short write, filesystem full?");
		return BT_FAIL;
	}

	if ((bt->size = lseek(bt->fd, 0, SEEK_END)) == -1) {
		DPRINTF("failed to update file size: %s", strerror(errno));
		bt->size = 0;
	}
	assert(mp->page->pgno== (bt->size/bt->head.psize-1));
	bt->meta_pgno=mp->page->pgno;

	return BT_SUCCESS;
}

/* Returns true if page p is a valid meta page, false otherwise.
 */
static int btree_is_meta_page(struct page *p)
{
	struct bt_meta	*m;
	unsigned char	 hash[SHA1_DIGEST_LENGTH];

	m = METADATA(p);
	if (!F_ISSET(p->flags, P_META)) {
		DPRINTF("page %d not a meta page", p->pgno);
		errno = EINVAL;
		return 0;
	}

	if (m->root >= p->pgno && m->root != P_INVALID) {
		DPRINTF("page %d points to an invalid root page", p->pgno);
		errno = EINVAL;
		return 0;
	}

	sha1((unsigned char *)m, METAHASHLEN, hash);
	if (bcmp(hash, m->hash, SHA1_DIGEST_LENGTH) != 0) {
		DPRINTF("page %d has an invalid digest", p->pgno);
		errno = EINVAL;
		return 0;
	}

	return 1;
}

static int btree_read_meta(struct btree *bt, pgno_t *p_next)
{
	struct mpage	*mp;
	
	pgno_t		  next_pgno;
	off_t		 size;

	assert(bt != NULL);

	if ((size = lseek(bt->fd, 0, SEEK_END)) == -1)
		goto fail;

	//DPRINTF("btree_read_meta: size = %llu", size);

	if (size < bt->size) {
		DPRINTF("file has shrunk!");
		errno = EIO;
		goto fail;
	}

	if (size == bt->head.psize) {		/* there is only the header */
		if (p_next != NULL)
			*p_next = 1;
		return BT_SUCCESS;		/* new file */
	}

	next_pgno = size / bt->head.psize;
	if (next_pgno == 0) {
		DPRINTF("corrupt file");
		errno = EIO;
		goto fail;
	}

	pgno_t meta_pgno = next_pgno - 1;

	if (size % bt->head.psize != 0) {
		DPRINTF("filesize not a multiple of the page size!");
		bt->flags |= BT_FIXPADDING;
		next_pgno++;
	}

	if (p_next != NULL)
		*p_next = next_pgno;

	if (size == bt->size) {
		DPRINTF("size unchanged, keeping current meta page");
		if (F_ISSET(bt->meta.flags, BT_TOMBSTONE)) {
			DPRINTF("file is dead");
			errno = ESTALE;
			return BT_FAIL;
		} else
			return BT_SUCCESS;
	}
	bt->size = size;

	while (meta_pgno > 0) {
		if ((mp = btree_get_mpage(bt, meta_pgno)) == NULL)
			break;
		if (btree_is_meta_page(mp->page)) {
			const struct bt_meta	* const meta = METADATA(mp->page);
			//DPRINTF("flags = 0x%x", meta->flags);
			if (F_ISSET(meta->flags, BT_TOMBSTONE)) {
				DPRINTF("file is dead");
				errno = ESTALE;
				return BT_FAIL;
			} else {
				/* Make copy of last meta page. */
				bt->meta_pgno=mp->page->pgno;
				assert(bt->meta_pgno);
				memcpy(&bt->meta, meta, sizeof(bt->meta));
				return BT_SUCCESS;
			}
		}else{
			DPRINTF("page %u not meta page, and continue reading backward",mp->pgno);
		}
		--meta_pgno;	/* scan backwards to first valid meta page */
	}

	errno = EIO;
fail:
	if (p_next != NULL)
		*p_next = P_INVALID;
	return BT_FAIL;
}

struct btree * btree_open_fd(int fd, unsigned int flags)
{
	struct btree	*bt;
	int		 fl;

	fl = fcntl(fd, F_GETFL, 0);
	if (fcntl(fd, F_SETFL, fl | O_APPEND) == -1)
		return NULL;

	if ((bt = calloc(1, sizeof(*bt))) == NULL)
		return NULL;
	bt->fd = fd;
	bt->flags = flags;
	bt->flags &= ~BT_FIXPADDING;
	bt->ref = 1;
	bt->meta.root = P_INVALID;

	if ((bt->page_cache = calloc(1, sizeof(*bt->page_cache))) == NULL)
		goto fail;
	bt->stat.max_cache = BT_MAXCACHE_DEF;
	RB_INIT(bt->page_cache);

	if ((bt->lru_queue = calloc(1, sizeof(*bt->lru_queue))) == NULL)
		goto fail;
	TAILQ_INIT(bt->lru_queue);

	if (btree_read_header(bt) != 0) {
		if (errno != ENOENT)
			goto fail;
		DPRINTF("new database");
		btree_write_header(bt, bt->fd);
	}

	if (btree_read_meta(bt, NULL) != 0)
		goto fail;

	DPRINTF("opened database version %u, pagesize %u",
	    bt->head.version, bt->head.psize);
	const size_t created_at= bt->meta.created_at;
	DPRINTF("timestamp: %s", ctime(&created_at));
	DPRINTF("depth: %u", bt->meta.depth);
	DPRINTF("entries: %lu", bt->meta.entries);
	DPRINTF("revisions: %u", bt->meta.revisions);
	DPRINTF("branch pages: %u", bt->meta.branch_pages);
	DPRINTF("leaf pages: %u", bt->meta.leaf_pages);
	DPRINTF("overflow pages: %u", bt->meta.overflow_pages);
	DPRINTF("root: %u", bt->meta.root);
	DPRINTF("previous meta page: %u", bt->meta.prev_meta);

	return bt;

fail:
	free(bt->lru_queue);
	free(bt->page_cache);
	free(bt);
	return NULL;
}

struct btree * btree_open(const char *path, unsigned int flags, mode_t mode)
{
	int		 fd, oflags;
	struct btree	*bt;

	if (F_ISSET(flags, BT_RDONLY))
		oflags = O_RDONLY;
	else
		oflags = O_RDWR | O_CREAT | O_APPEND;

	if ((fd = open(path, oflags, mode)) == -1)
		return NULL;

	if ((bt = btree_open_fd(fd, flags)) == NULL)
		close(fd);
	else {
		bt->path = strdup(path);
		DPRINTF("opened btree %p", bt);
	}

	return bt;
}

static void btree_ref(struct btree *bt)
{
	bt->ref++;
	DPRINTF("ref is now %d on btree %p", bt->ref, bt);
}

void btree_close(struct btree *bt)
{
	if (bt == NULL)
		return;

	if (--bt->ref == 0) {
		printf("ref is zero, closing btree %p\n", bt);
		close(bt->fd);
		mpage_flush(bt);
		free(bt->lru_queue);
		free(bt->path);
		free(bt->page_cache);
		free(bt);
	} else
		DPRINTF("ref is now %d on btree %p", bt->ref, bt);
}
static inline unsigned int get_page_left_size(struct page* page){
	return page->upper-page->lower;
}
static inline unsigned int get_page_keys_count(struct page* page){
	return (page->lower-offsetof(struct page, offsets))>>1;
}
static inline struct node * get_node_n(struct page *page, unsigned int i){
	const unsigned int __max= get_page_keys_count(page);
	assert(i>=0 && i<__max);
	return (struct node*)((char*)page+page->offsets[i]);
}
static inline struct mpage* get_child_mpage(struct btree* bt, const struct mpage* parent, indx_t i){
	assert(parent);
	assert(i<get_page_keys_count(parent->page));
	assert(i >=0);
	struct node *node=  get_node_n(parent->page,i);
	struct mpage*mp = btree_get_mpage(bt,node->p.np_pgno);
	if(!mp) return mp;
	mp->parent=(struct mpage*)parent;
	mp->parent_index=i;
	return mp;
}
static inline struct mpage * get_right_sibling_mpage(struct btree*bt,struct mpage * mp){
	assert(mp->parent);
	assert(mp->parent_index<get_page_keys_count(mp->parent->page)-1 && mp->parent_index>=0);
	struct mpage * right_page=get_child_mpage(bt,mp->parent,mp->parent_index+1);
	return right_page;
}
static inline struct mpage * get_left_sibling_mpage(struct btree*bt,struct mpage * mp){
	assert(mp->parent);
	assert(mp->parent_index<get_page_keys_count(mp->parent->page) && mp->parent_index>0);
	struct mpage * left_mpage=get_child_mpage(bt,mp->parent,mp->parent_index-1);
	return left_mpage;
}

static int btree_search_in_branch_page(struct btree *bt, const struct mpage *mp, struct btval *key, unsigned int *kip)
{
	assert(IS_BRANCH(mp));
	unsigned int	 i = 0;
	int		 low, high;
	int		 rc = 0;
	struct node	*node;
	struct btval	 nodekey;

	DPRINTF("searching in %lu keys in branch page %u ",NUMKEYS(mp), mp->pgno);

	assert(NUMKEYS(mp) > 0);

	memset(&nodekey, 0, sizeof(nodekey));
	// k0 p0 k1 p1 k2 p2 k3 p3 
	low =  1;
	high = ((mp->page->lower - PAGEHDRSZ) >> 1) -1; //NUMKEYS(mp) - 1;
	while (low <= high) {
		i = (low + high) >> 1;
		node = get_node_n(mp->page,i);//NODEPTR(mp, i);

		nodekey.size = node->ksize;
		nodekey.data = (void *)(node->data);//NODEKEY(node);

		if (bt->cmp)
			rc = bt->cmp(key, &nodekey);
		else
			rc = bt_cmp(bt, key, &nodekey);

		//DPRINTF("checking branch key: %u [%.*s -> %u]",i, (int)node->ksize, (char *)NODEKEY(node),node->n_pgno);

		if (rc == 0)
			break;
		if (rc > 0)
			low = i + 1;
		else
			high = i - 1;
	}
/// a b c d
// 0  1  2  3 
	if (kip)	/* Store the key index if requested. */
		*kip = i;
		// i : 0 - n-1
	return rc; //NODEPTR(mp, i);
}

/* Search for key within a leaf page, using binary search.
 * Returns the smallest entry larger or equal to the key.
 * If exactp is non-null, stores whether the found entry was an exact match
 * in *exactp (1 or 0).
 * If kip is non-null, stores the index of the found entry in *kip.
 * If no entry larger of equal to the key is found, returns NULL.
 */
static struct node * btree_search_in_leaf_page(struct btree *bt, struct mpage *mp, struct btval *key,int *exactp, unsigned int *kip)
{
	assert(IS_LEAF(mp));
	unsigned int	 i = 0;
	int		 low, high;
	int		 rc = 0;
	struct node	*node;
	struct btval	 nodekey;

	DPRINTF("searching  in %lu keys in leaf page %u ",NUMKEYS(mp), mp->pgno);

	assert(NUMKEYS(mp) > 0);

	memset(&nodekey, 0, sizeof(nodekey));
	// k0 p0 k1 p1 k2 p2 k3 p3 
	low = 0;
	high = ((mp->page->lower - PAGEHDRSZ) >> 1) -1; //NUMKEYS(mp) - 1;
	while (low <= high) {
		i = (low + high) >> 1;
		node = (struct node *)((char *)(mp->page) + mp->page->offsets[i]);//NODEPTR(mp, i);

		nodekey.size = node->ksize;
		nodekey.data = (void *)(node->data);//NODEKEY(node);

		if (bt->cmp)
			rc = bt->cmp(key, &nodekey);
		else
			rc = bt_cmp(bt, key, &nodekey);

		//DPRINTF("comparing leaf key index %u [%.*s]",i, (int)nodekey.size, (char *)nodekey.data);

		if (rc == 0)
			break;
		if (rc > 0)
			low = i + 1;
		else
			high = i - 1;
	}
/// a b c d
	if (rc > 0) {
		//high low
		/* Found entry is less than the key. */
		i++;	/* Skip to get the smallest entry larger than key. */
		assert(i==low);
		
		if (i >= NUMKEYS(mp))
			/* There is no entry larger or equal to the key. */
			{
				assert(i==NUMKEYS(mp));
				return NULL;
			}
	}
	if (exactp)
		*exactp = (rc == 0);
	if (kip)	/* Store the key index if requested. */
		*kip = i;
		// i : 0 - n-1
	return (struct node *)((char *)(mp->page) + mp->page->offsets[i]); //NODEPTR(mp, i);
}

static void cursor_pop_page(struct cursor *cursor)
{
	//struct ppage	*top = CURSOR_TOP(cursor);
	// SLIST_REMOVE_HEAD(&cursor->stack, entry);//CURSOR_POP(cursor);
		
	  	struct page_stack* head= &cursor->stack;
	  	struct ppage* top_ppage= head->slh_first;
		head->slh_first = top_ppage->entry.sle_next;		

	top_ppage->mpage->ref--;

	DPRINTF("popped page %u off cursor %p", top_ppage->mpage->pgno, cursor);

	free(top_ppage);
}

static struct ppage * cursor_push_page(struct cursor *cursor, struct mpage *mp)
{
	

	DPRINTF("pushing page %u on cursor %p", mp->pgno, cursor);
	struct ppage	*ppage;
	if ((ppage = calloc(1, sizeof(*ppage))) == NULL)
		return NULL;
	ppage->mpage = mp;
	mp->ref++;
	// SLIST_INSERT_HEAD(&cursor->stack, ppage, entry);//CURSOR_PUSH(cursor, ppage);
	  struct page_stack * const head=&cursor->stack;
	 ppage->entry.sle_next = head->slh_first;			
	head->slh_first = ppage;					
	return ppage;
}

static struct mpage * btree_get_mpage(struct btree *bt, pgno_t pgno)
{
	struct mpage	*mp;

	mp = mpage_lookup(bt, pgno);
	if (mp == NULL) {
		if ((mp = calloc(1, sizeof(*mp))) == NULL)
			return NULL;
		if ((mp->page = malloc(bt->head.psize)) == NULL) {
			free(mp);
			return NULL;
		}
		if (__btree_read_page(bt, pgno, mp->page) != BT_SUCCESS) {
			mpage_free(mp);
			return NULL;
		}
		mp->pgno = pgno;
		mpage_add(bt, mp);
	} //else
		//DPRINTF("returning page %u from cache", pgno);

	return mp;
}
static int btree_search_first_leaf_key(struct btree *bt, const struct mpage *root, struct btval *key)
{
	const struct mpage	*mp = root;
	while (IS_BRANCH(mp)) {
		const struct mpage* const first_mpage =get_child_mpage(bt, mp, 0);
		if (first_mpage== NULL)
			return BT_FAIL;
		mp=first_mpage;
		///abc -> abcd
	}

	if (!IS_LEAF(mp)) {
		DPRINTF("internal error, index points to a %02X page!?",mp->page->flags);
		return BT_FAIL;
	}

	struct node	*node=get_node_n(mp->page,0);
	key->size=node->ksize;
	key->data=node->data;

	return BT_SUCCESS;
}

static int btree_search_leaf_page_from_root(struct btree *bt, struct mpage *root, struct btval *key,
    struct cursor *cursor, int modify, struct mpage **mpp)
{
	struct mpage	*mp, *parent;

	if (cursor && cursor_push_page(cursor, root) == NULL)
		return BT_FAIL;

	mp = root;
	while (IS_BRANCH(mp)) {
		unsigned int	 i = 0;
		struct node	*node;

		DPRINTF("branch page %u has %lu keys", mp->pgno, NUMKEYS(mp));
		assert(NUMKEYS(mp) > 1);
		//DPRINTF("found index 0 to page %u", NODEPGNO(NODEPTR(mp, 0)));

		if (key == NULL)	/* Initialize cursor to first page. */
			i = 0;
		else {
			//k0 p0 k1 p1 k2 p2 k3 p3 
			const int rc = btree_search_in_branch_page(bt, mp, key, &i);
			if(rc<0){
				assert(i>0);
				--i;
			}
		}

		//if (key)
		//	DPRINTF("following index %u for key %.*s",i, (int)key->size, (char *)key->data);
		assert((int)i >= 0 && i < NUMKEYS(mp));
		node = NODEPTR(mp, i);

		if (cursor)
			CURSOR_TOP(cursor)->ki = i;

		parent = mp;
		if ((mp = btree_get_mpage(bt,  node->p.np_pgno)) == NULL)
			return BT_FAIL;
		mp->parent = parent;
		mp->parent_index = i;
		///abc -> abcd

		if (cursor && cursor_push_page(cursor, mp) == NULL)
			return BT_FAIL;

		if (modify && (mp = mpage_copy_on_write(bt, mp)) == NULL)
			return BT_FAIL;
	}

	if (!IS_LEAF(mp)) {
		DPRINTF("internal error, index points to a %02X page!?",mp->page->flags);
		return BT_FAIL;
	}

	DPRINTF("found leaf page %u for key %.*s", mp->pgno,key ? (int)key->size : 0, key ? (char *)key->data : NULL);

	*mpp = mp;
	return BT_SUCCESS;
}

/* Search for the page a given key should be in.
 * Stores a pointer to the found page in *mpp.
 * If key is NULL, search for the lowest page (used by btree_cursor_first).
 * If cursor is non-null, pushes parent pages on the cursor stack.
 * If modify is true, visited pages are updated with new page numbers.
 */
static int btree_search_leaf_page(struct btree *bt, struct btree_txn *txn, struct btval *key,
    struct cursor *cursor, int modify, struct mpage **mpp)
{
	int		 rc;
	pgno_t		 root;
	
	/* Choose which root page to start with. If a transaction is given
         * use the root page from the transaction, otherwise read the last
         * committed root page.
	 */
	assert(txn);
	assert(bt);
	if (F_ISSET(txn->flags, BT_TXN_ERROR)) {
		DPRINTF("transaction has failed, must abort");
		errno = EINVAL;
		return BT_FAIL;
	} else
		root = txn->root;

	if (root == P_INVALID) {		/* Tree is empty. */
		DPRINTF("tree is empty");
		errno = ENOENT;
		return BT_FAIL;
	}
	struct mpage	*root_page;

	if ((root_page = btree_get_mpage(bt, root)) == NULL)
		return BT_FAIL;

	//DPRINTF("root page has flags 0x%X", mp->page->flags);

	assert(root_page->parent == NULL);

	if (modify && !root_page->dirty) {
		if ((root_page = mpage_copy_on_write(bt, root_page)) == NULL)
			return BT_FAIL;
		txn->root = root_page->pgno;
	}

	return btree_search_leaf_page_from_root(bt, root_page, key, cursor, modify, mpp);
}

static int btree_read_data(struct btree *bt, struct mpage *mp, struct node *leaf,struct btval *data)
{
	struct mpage	*omp;		/* overflow mpage */
	size_t		 psz;
	size_t		 max;

	memset(data, 0, sizeof(*data));
	max = bt->head.psize - PAGEHDRSZ;

	if (!F_ISSET(leaf->flags, F_BIGDATA)) {
		data->size = leaf->n_dsize;
		if (data->size > 0) {
			if (mp == NULL) {
				if ((data->data = malloc(data->size)) == NULL)
					return BT_FAIL;
				memcpy(data->data, NODEDATA(leaf), data->size);
				data->free_data = 1;
				data->mp = NULL;
			} else {
				data->data = (void *)((char *)leaf->data + leaf->ksize);//NODEDATA(leaf);
				data->free_data = 0;
				data->mp = mp;
				mp->ref++;
			}
		}
		return BT_SUCCESS;
	}

	/* Read overflow data.
	 */
	DPRINTF("allocating %u byte for overflow data", leaf->n_dsize);
	if ((data->data = malloc(leaf->n_dsize)) == NULL)
		return BT_FAIL;
	data->size = leaf->n_dsize;
	data->free_data = 1;
	data->mp = NULL;
	pgno_t		 pgno;
	size_t		 sz = 0;
	memcpy(&pgno, NODEDATA(leaf), sizeof(pgno));
	for (sz = 0; sz < data->size; ) {
		if ((omp = btree_get_mpage(bt, pgno)) == NULL ||
		    !F_ISSET(omp->page->flags, P_OVERFLOW)) {
			DPRINTF("read overflow page %u failed", pgno);
			free(data->data);
			mpage_del(bt,omp);
			return BT_FAIL;
		}
		psz = data->size - sz;
		if (psz > max)
			psz = max;
		memcpy((char *)data->data + sz, omp->page->offsets, psz);
		sz += psz;
		pgno = omp->page->p_next_pgno;
	}

	return BT_SUCCESS;
}

int btree_txn_get( struct btree_txn *txn,struct btval *key, struct btval *data)
{
	int		 rc, exact;
	struct node	*leaf;
	struct mpage	*mp;
	assert(txn);
	assert(key);
	assert(data);
	DPRINTF("===> get key [%.*s]", (int)key->size, (char *)key->data);
	struct btree* const bt=txn->bt;

	if (key->size == 0 || key->size > MAXKEYSIZE) {
		errno = EINVAL;
		return BT_FAIL;
	}

	if ((rc = btree_search_leaf_page(bt, txn, key, NULL, 0, &mp)) != BT_SUCCESS)
		return rc;

	leaf = btree_search_in_leaf_page(bt, mp, key, &exact, NULL);
	if (leaf && exact)
		rc = btree_read_data(bt, mp, leaf, data);
	else {
		errno = ENOENT;
		rc = BT_FAIL;
	}

	mpage_prune(bt);
	return rc;
}
static inline void print_cursor(const struct ppage*top){
	DPRINTF("cursor: page:%u,ki:%u/%u", top->mpage->page->pgno,top->ki,get_page_keys_count(top->mpage->page)-1);
}
static int btree_sibling(struct cursor *cursor, int move_right)
{
	int		 rc;
	

	struct mpage	*mp;

	struct ppage* const top = CURSOR_TOP(cursor);
	struct ppage	*parent;
	//((elm)->field.sle_next)
	if ((parent = top->entry.sle_next/*SLIST_NEXT(top, entry)*/) == NULL) {
		errno = ENOENT;
		return BT_FAIL;			/* root has no siblings */
	}

	print_cursor(parent);

	cursor_pop_page(cursor);

	if (move_right ? (parent->ki + 1 >= NUMKEYS(parent->mpage)) : (parent->ki == 0)) {
		DPRINTF("cursor: moving to %s cousin page", move_right ? "right" : "left");
		if ((rc = btree_sibling(cursor, move_right)) != BT_SUCCESS)
			return rc;
		parent = CURSOR_TOP(cursor);
	} else {
		if (move_right)
			parent->ki++;
		else
			parent->ki--;
		DPRINTF("cursor: moving to %s sibling index key %u", move_right ? "right" : "left", parent->ki);
	}
	assert(IS_BRANCH(parent->mpage));

	//indx = NODEPTR(parent->mpage, parent->ki);
	const struct node* const indx = (struct node*)((char*)parent->mpage->page + parent->mpage->page->offsets[parent->ki]);
	if ((mp = btree_get_mpage(cursor->bt, indx->n_pgno)) == NULL)
		return BT_FAIL;
	mp->parent = parent->mpage;
	mp->parent_index = parent->ki;

	cursor_push_page(cursor, mp);

	return BT_SUCCESS;
}

static int bt_set_key(struct btree *bt, struct mpage *mp, struct node *node,
    struct btval *key)
{
	if (key == NULL)
		return 0;

	 {
		key->size = node->ksize;
		key->data = NODEKEY(node);
		key->free_data = 0;
		key->mp = mp;
		mp->ref++;
	}

	return 0;
}

static int btree_cursor_next(struct cursor *cursor, struct btval *key, struct btval *data)
{

	if (cursor->eof) {
		errno = ENOENT;
		return BT_FAIL;
	}

	assert(cursor->initialized);

	struct ppage	* top = SLIST_FIRST(&cursor->stack);//CURSOR_TOP(cursor);

	print_cursor(top);

	if (top->ki + 1 >= NUMKEYS(top->mpage)) {
		//DPRINTF("=====> move to next sibling page");
		if (btree_sibling(cursor, 1) != BT_SUCCESS) {
			cursor->eof = 1;
			DPRINTF("cursor: eof");
			return BT_FAIL;
		}
		top = CURSOR_TOP(cursor);
		print_cursor(top);
	} else
		top->ki++;

	print_cursor(top);

	assert(IS_LEAF(top->mpage));
	struct node	*const leaf = NODEPTR(top->mpage, top->ki);

	if (data && btree_read_data(cursor->bt, top->mpage, leaf, data) != BT_SUCCESS)
		return BT_FAIL;

	if (bt_set_key(cursor->bt, top->mpage, leaf, key) != 0)
		return BT_FAIL;

	return BT_SUCCESS;
}

static int btree_cursor_set(struct cursor *cursor, struct btval *key, struct btval *data,int *exactp)
{
	int		 rc;
	
	struct mpage	*mp;
	struct ppage	*top;

	assert(cursor);
	assert(key);
	assert(key->size > 0);

	rc = btree_search_leaf_page(cursor->bt, cursor->txn, key, cursor, 0, &mp);
	if (rc != BT_SUCCESS)
		return rc;
	assert(IS_LEAF(mp));

	top = CURSOR_TOP(cursor);
	struct node	*leaf = btree_search_in_leaf_page(cursor->bt, mp, key, exactp, &top->ki);
	if (exactp != NULL && !*exactp) {
		/* BT_CURSOR_EXACT specified and not an exact match. */
		errno = ENOENT;
		return BT_FAIL;
	}

	if (leaf == NULL) {
		DPRINTF("===> inexact leaf not found, goto sibling");
		if (btree_sibling(cursor, 1) != BT_SUCCESS)
			return BT_FAIL;		/* no entries matched */
		top = CURSOR_TOP(cursor);
		top->ki = 0;
		mp = top->mpage;
		assert(IS_LEAF(mp));
		leaf = NODEPTR(mp, 0);
	}

	cursor->initialized = 1;
	cursor->eof = 0;

	if (data && btree_read_data(cursor->bt, mp, leaf, data) != BT_SUCCESS)
		return BT_FAIL;

	if (bt_set_key(cursor->bt, mp, leaf, key) != 0)
		return BT_FAIL;
	DPRINTF("==> cursor placed on key %.*s",
	    (int)key->size, (char *)key->data);

	return BT_SUCCESS;
}

static int btree_cursor_first(struct cursor *cursor, struct btval *key, struct btval *data)
{
	int		 rc;
	struct mpage	*mp;
	struct node	*leaf;

	rc = btree_search_leaf_page(cursor->bt, cursor->txn, NULL, cursor, 0, &mp);
	if (rc != BT_SUCCESS)
		return rc;
	assert(IS_LEAF(mp));

	leaf = NODEPTR(mp, 0);
	cursor->initialized = 1;
	cursor->eof = 0;

	if (data && btree_read_data(cursor->bt, mp, leaf, data) != BT_SUCCESS)
		return BT_FAIL;

	if (bt_set_key(cursor->bt, mp, leaf, key) != 0)
		return BT_FAIL;

	return BT_SUCCESS;
}

int btree_cursor_get(struct cursor *cursor, struct btval *key, struct btval *data,enum cursor_op op)
{
	int		 rc;
	int		 exact = 0;

	assert(cursor);

	switch (op) {
	case BT_CURSOR:
	case BT_CURSOR_EXACT:
		while (SLIST_FIRST(&cursor->stack) != NULL)
			cursor_pop_page(cursor);
		if (key == NULL || key->size == 0 || key->size > MAXKEYSIZE) {
			errno = EINVAL;
			rc = BT_FAIL;
		} else if (op == BT_CURSOR_EXACT)
			rc = btree_cursor_set(cursor, key, data, &exact);
		else
			rc = btree_cursor_set(cursor, key, data, NULL);
		break;
	case BT_NEXT:
		if (!cursor->initialized)
			rc = btree_cursor_first(cursor, key, data);
		else
			rc = btree_cursor_next(cursor, key, data);
		break;
	case BT_FIRST:
		while (CURSOR_TOP(cursor) != NULL)
			cursor_pop_page(cursor);
		rc = btree_cursor_first(cursor, key, data);
		break;
	default:
		DPRINTF("unhandled/unimplemented cursor operation %u", op);
		rc = BT_FAIL;
		break;
	}

	mpage_prune(cursor->bt);

	return rc;
}

static inline bool is_db_empty(struct btree *bt){
	return bt->txn? bt->txn->root == P_INVALID : bt->meta.root == P_INVALID;
}
static inline struct mpage* new_root_page(struct btree_txn * txn ){
	struct mpage * mp;
	if ((mp = btree_new_page(txn->bt, is_db_empty(txn->bt)? P_LEAF : P_BRANCH)) == NULL) {
			return mp;
		}
	txn->root = mp->pgno;
	txn->bt->meta.depth++;
	DPRINTF("allocating new root page %u",mp->pgno);
	return mp;
}
static struct mpage * btree_new_page(struct btree *bt, uint32_t flags)
{
	struct mpage	*mp;

	assert(bt != NULL);
	assert(bt->txn != NULL);

	DPRINTF("allocating new mpage  page no %u",bt->txn->next_pgno);
	if ((mp = calloc(1, sizeof(*mp))) == NULL)
		return NULL;
	if ((mp->page = malloc(bt->head.psize)) == NULL) {
		free(mp);
		return NULL;
	}
	mp->pgno = mp->page->pgno = bt->txn->next_pgno++;
	mp->page->flags = flags;
	mp->page->lower = PAGEHDRSZ;
	mp->page->upper = bt->head.psize;

	if (IS_BRANCH(mp))
		bt->meta.branch_pages++;
	else if (IS_LEAF(mp))
		bt->meta.leaf_pages++;
	else if (IS_OVERFLOW(mp))
		bt->meta.overflow_pages++;

	mpage_add(bt, mp);
	mpage_dirty(bt->txn, mp);

	return mp;
}

static inline size_t bt_leaf_size(struct btree *bt, struct btval *key, struct btval *data)
{
	size_t		 sz =  offsetof(struct node,data) + key->size; //+ ;//LEAFSIZE(key, data);
	if (data->size >= bt->head.psize / BT_MINKEYS) {
		/* put on overflow page */
		sz += sizeof(pgno_t);
	}else{
		sz+=data->size;
	}

	return sz + sizeof(indx_t); // key_size, data_size, offset_size
}

static inline size_t bt_branch_size(struct btree *bt, struct btval *key)
{
	size_t		 sz=offsetof(struct node,data)+ (key?key->size:0);

	//sz = INDXSIZE(key);
	if (sz >= bt->head.psize / BT_MINKEYS) {
		/* put on overflow page */
		/* not implemented */
		/* sz -= key->size - sizeof(pgno_t); */
	}

	return sz + sizeof(indx_t);
}

static int btree_write_overflow_data(struct btree *bt, struct page *p, struct btval *data)
{
	
	size_t		 sz;
	
	struct mpage	*next = NULL;

	const size_t	max = bt->head.psize - PAGEHDRSZ;
	size_t		 done = 0;
	while (done < data->size) {
		if (next != NULL)
			p = next->page;

		if (data->size - done > max) {
			/* need another overflow page */
			if ((next = btree_new_page(bt, P_OVERFLOW)) == NULL)
				return BT_FAIL;
			p->b.pb_next_pgno = next->pgno;
			DPRINTF("linking overflow page %u", next->pgno);
		} else
			p->b.pb_next_pgno = 0;		/* indicates end of list */
		sz = data->size - done;
		if (sz > max)
			sz = max;
		DPRINTF("copying %zu bytes to overflow page %u", sz, p->pgno);
		memcpy(p->offsets, (char *)data->data + done, sz);
		done += sz;
	}

	return BT_SUCCESS;
}

static inline unsigned int calculate_branch_node_size(const struct btval *key)
{
	unsigned int sz =  offsetof(struct node, data) + (key ? key->size : 0);
	return sz;
}

static inline unsigned int calculate_new_node_size(bool branch,size_t page_size,const struct btval *key, struct btval *data)
{
	unsigned int sz =  offsetof(struct node, data) + (key ? key->size : 0);
	if(!branch){
		const bool overflowed_data = data->size >= page_size/ BT_MINKEYS;
		if( overflowed_data ){
			sz+=sizeof(pgno_t);
		}else{
			sz+=data->size;
		}
	}
	return sz;

}
static inline unsigned int calculate_node_size(bool branch,size_t page_size,const struct btval *key, struct btval *data,int flags)
{
	unsigned int sz =  offsetof(struct node, data) + (key ? key->size : 0);
	
	if(!branch){
		const bool overflowed_data = data->size >= page_size/ BT_MINKEYS;
		if( overflowed_data || flags & F_BIGDATA){
			sz+=sizeof(pgno_t);
		}else{
			sz+=data->size;
		}
	}
	return sz;

}
static inline unsigned int calculate_existent_node_size(bool branch, const struct node * node)
{
	assert(branch || node->ksize>0);
	unsigned int sz =  offsetof(struct node, data) + node->ksize;
	if(!branch ){
		if(node->flags & F_BIGDATA){
			sz+=sizeof(pgno_t);
		}else{
			sz+=node->p.np_dsize;
		}
	}//for branch node, next_page_no is in the node header
	return sz;

}
static inline void __init_branch_node(struct node * node,const struct btval *sep_key,  pgno_t pgno)
{
	node->ksize = sep_key? sep_key->size:0;
	node->flags = 0;
	node->p.np_pgno = pgno;
	if(sep_key)
		memcpy(node->data, sep_key->data, sep_key->size);
}
static inline int __init_leaf_node(struct btree*bt,struct node * node,const struct btval *key, struct btval *data)
{
	assert(key&& key->size);
	node->ksize =  key->size;
	node->p.np_dsize = data->size;
	memcpy(node->data, key->data, key->size);

	const bool overflowed_data = data->size >= bt->head.psize/ BT_MINKEYS;
	if(overflowed_data){
			struct mpage * const ofp= btree_new_page(bt, P_OVERFLOW);
			if (ofp == NULL)
				return BT_FAIL;
			DPRINTF("data size is %zu, put on overflow page %u",data->size, ofp->pgno);
			
			memcpy(node->data + node->ksize , &ofp->pgno,sizeof(pgno_t));
			if (btree_write_overflow_data(bt, ofp->page,data) == BT_FAIL)
				return BT_FAIL;
	}else{
			memcpy(node->data + node->ksize, data->data,data->size);
	}
	node->flags = overflowed_data ? F_BIGDATA:0;
	return BT_SUCCESS;
}

static inline int __init_leaf_node_from_old_leaf_node(struct node * node, const struct node * old_node)
{
	node->ksize =  old_node->ksize;
	node->flags=	old_node->flags;
	node->p.np_dsize = old_node->p.np_dsize;

	memcpy(node->data, old_node->data, node->ksize);

	
	if(old_node->flags & F_BIGDATA){
			memcpy(node->data + node->ksize ,old_node->data+old_node->ksize,sizeof(pgno_t));
	}else{
			memcpy(node->data + node->ksize, old_node->data,old_node->p.np_dsize);
	}
	return BT_SUCCESS;
}

static int btree_insert_branch_node(struct btree *bt, struct mpage *mp, indx_t indx, struct btval * sep_key, pgno_t pgno)
{
	assert(IS_BRANCH(mp));
	assert(mp->dirty);
	return btree_insert_node(bt,mp,indx,sep_key,NULL,pgno,0);
}

static int btree_insert_new_leaf_node(struct btree *bt, struct mpage *mp, indx_t indx, const struct btval *key, struct btval *data)
{
	assert(IS_LEAF(mp));
	assert(data);
	assert(key);
	return  btree_insert_node(bt,mp,indx,key,data,0/*pgno*/, 0);
}


static int btree_insert_node(struct btree *bt, struct mpage *mp, indx_t indx, const struct btval *key, struct btval *data, pgno_t pgno, uint8_t flags)
{
	assert(mp->dirty);
	struct page	* const p = mp->page;
	assert(p->upper >= p->lower);
	assert(key || indx==0);
	DPRINTF("%s page %u :insert node [%.*s] to index %i, key size %zu", IS_LEAF(mp) ? "leaf" : "branch", mp->pgno,
		key ? (int)key->size : 0, key ? (char *)key->data : NULL, 
	     indx, key ? key->size : 0);

	struct mpage	*ofp = NULL;		/* overflow page */
	const ssize_t	 node_size = calculate_node_size(IS_BRANCH(mp), bt->head.psize, key,data,flags );
	if (IS_LEAF(mp)) {
		assert(data);
	
		if (data->size >= bt->head.psize / BT_MINKEYS) {
			/* Put data on overflow page. */
			DPRINTF("data size is %zu, put on overflow page",data->size);
			
			if ((ofp = btree_new_page(bt, P_OVERFLOW)) == NULL)
				return BT_FAIL;
			DPRINTF("allocated overflow page %u", ofp->pgno);
			flags |= F_BIGDATA;
		}
	}
	assert(p==mp->page);
	const unsigned n = get_page_keys_count(mp->page);
	assert(indx<=n);
	const indx_t left_size=  get_page_left_size(mp->page);
	if (node_size + sizeof(indx_t) > left_size) {
		DPRINTF("not enough room in page %u, got %lu offsets, left_size:%u,node size = %zu",mp->pgno, NUMKEYS(mp),left_size,node_size);
		return BT_FAIL;
	}
	//abcde
	if(key &&  !bt->cmp){
		if(indx<n){
			struct node * next_node=get_node_n(mp->page,indx);
			struct btval next_key; next_key.size=next_node->ksize; next_key.data=next_node->data;
			assert(bt_cmp(bt,&next_key,key)>0);
		}
		if(indx>=1){//index-1>=0
			struct node * prev_node=get_node_n(mp->page,indx-1);
			struct btval prev_key; prev_key.size=prev_node->ksize; prev_key.data=prev_node->data;
			assert(bt_cmp(bt,key,&prev_key)>0);
		}
	}
	/* Move higher pointers up one slot. */
	for (unsigned int	 i = NUMKEYS(mp); i > indx; i--)
		p->offsets[i] = p->offsets[i - 1];

	/* Adjust free space offsets. */
	const indx_t		 ofs = p->upper - node_size;
	assert(ofs >= p->lower + sizeof(indx_t));
	p->offsets[indx] = ofs;
	p->upper = ofs;
	p->lower += sizeof(indx_t);

	/* Write the node data. */
	struct node	* const node = get_node_n(p, indx);
	node->ksize = (key == NULL) ? 0 : key->size;
	node->flags = flags;
	if (IS_LEAF(mp))
		node->p.np_dsize = data->size;
	else
		node->p.np_pgno = pgno;

	if (key)
		memcpy(NODEKEY(node), key->data, key->size);

	if (IS_LEAF(mp)) {
		assert(key);
		if (ofp == NULL) {
			if (F_ISSET(flags, F_BIGDATA))
				memcpy(node->data + key->size, data->data,sizeof(pgno_t));
			else
				memcpy(node->data + key->size, data->data,data->size);
		} else {
			memcpy(node->data + key->size, &ofp->pgno,sizeof(pgno_t));
			if (btree_write_overflow_data(bt, ofp->page,data) == BT_FAIL)
				return BT_FAIL;
		}
	}

	return BT_SUCCESS;
}

static void __btree_del_node(struct mpage *mp, indx_t indx)
{
	unsigned int	 sz;
	indx_t		 i, j, numkeys, ptr;
	
	char		*base;
	assert(mp->dirty==1);
	DPRINTF("delete node %u/%u on %s page %u", indx,get_page_keys_count(mp->page)-1,
		IS_LEAF(mp) ? "leaf" : "branch", mp->pgno);
	assert(indx < NUMKEYS(mp));
	//variable length
	//array heap
	///header, array, heap

	struct node	*node = get_node_n(mp->page,indx); //NODEPTR(mp, indx);
		const unsigned int left_size1=get_page_left_size(mp->page);
	const unsigned int node_size=calculate_existent_node_size(IS_BRANCH(mp),node);
	sz = offsetof(struct node, data) + node->ksize;
	if (IS_LEAF(mp)) {
		if (F_ISSET(node->flags, F_BIGDATA))
			sz += sizeof(pgno_t);
		else
			sz += node->p.np_dsize;// NODEDSZ(node);
	}

	ptr = mp->page->offsets[indx];
	numkeys = (mp->page->lower-offsetof(struct page,offsets))>>1;///NUMKEYS(mp);
	///a b c d e f  uvwxyz
	for (i = j = 0; i < numkeys; i++) {
		if (i != indx) {
			mp->page->offsets[j] = mp->page->offsets[i];
			if (mp->page->offsets[i] < ptr)
				mp->page->offsets[j] += sz;
			j++;
		}
	}

	base = (char *)mp->page + mp->page->upper;
	// xx y zzz
	//memcpy( upeer+sz,upper,ptr-upper)
	memcpy(base + sz, base, ptr - mp->page->upper);

	mp->page->lower -= sizeof(indx_t);
	mp->page->upper += sz;

	const unsigned int left_size2=get_page_left_size(mp->page);
	assert( left_size2-left_size1 == node_size + sizeof(indx_t));
}

struct cursor * btree_txn_cursor_open(struct btree_txn *txn)
{
	struct cursor	*cursor;


	if ((cursor = calloc(1, sizeof(*cursor))) != NULL) {
		SLIST_INIT(&cursor->stack);
		cursor->bt = txn->bt;
		cursor->txn = txn;
		btree_ref(txn->bt);
	}

	return cursor;
}

void btree_cursor_close(struct cursor *cursor)
{
	if (cursor != NULL) {
		while (!CURSOR_EMPTY(cursor))
			cursor_pop_page(cursor);

		btree_close(cursor->bt);
		free(cursor);
	}
}

static int btree_update_key(struct mpage *mp, indx_t indx,struct btval *key)
{
	indx_t			 ptr;
	int			 delta;
	size_t			 len;
	struct node		*node;
	char			*base;

	node = NODEPTR(mp, indx);
	ptr = mp->page->offsets[indx];
	DPRINTF("update sep key %u (offset %u) [%.*s] to [%.*s] on page %u",
	    indx, ptr,
	    (int)node->ksize, (char *)NODEKEY(node),
	    (int)key->size, (char *)key->data,
	    mp->pgno);

	if (key->size != node->ksize) {
		delta = key->size - node->ksize;
		if (delta > 0 && SIZELEFT(mp) < delta) {
			DPRINTF("OUCH! Not enough room, delta = %d", delta);
			return BT_FAIL;
		}

		const indx_t numkeys = NUMKEYS(mp);
		for (int i = 0; i < numkeys; i++) {
			if (mp->page->offsets[i] <= ptr)
				mp->page->offsets[i] -= delta;
		}

		base = (char *)mp->page + mp->page->upper;
		len = ptr - mp->page->upper + NODESIZE;
		memcpy(base - delta, base, len);
		mp->page->upper -= delta;

		node = NODEPTR(mp, indx);
		node->ksize = key->size;
	}

	memcpy(NODEKEY(node), key->data, key->size);

	return BT_SUCCESS;
}

/* Move a node from src to dst.
 */
static int btree_move_node(struct btree *bt, struct mpage *src_page, struct mpage *dst_page, bool is_tail)
{
	int			 rc;
	
	assert(src_page->parent);
	assert(dst_page->parent);
	assert(src_page->parent==dst_page->parent);
	indx_t src_index,dst_index;
	if(is_tail){
		assert(src_page->parent_index==dst_page->parent_index+1);
		src_index=0;
		dst_index=get_page_keys_count(dst_page->page);

	}else{
		assert(src_page->parent_index+1==dst_page->parent_index);
		src_index=get_page_keys_count(src_page->page)-1;
		dst_index=0;
	}

	const struct node* const srcnode = NODEPTR(src_page, src_index);
	DPRINTF("moving %s node %u [%.*s] on page %u to node %u on page %u",IS_LEAF(src_page) ? "leaf" : "branch",
	    src_index,
	    (int)srcnode->ksize, (char *)NODEKEY(srcnode),
	    src_page->pgno,
	    dst_index, dst_page->pgno);

	/* Mark src_page and dst_page as dirty. */
	if ((src_page = mpage_copy_on_write(bt, src_page)) == NULL ||
	    (dst_page = mpage_copy_on_write(bt, dst_page)) == NULL)
		return BT_FAIL;
	
/*			   	   3   6     9 
	  src page  2  3 4   6 7    9 10
	*/
	// s[i-1]<= x < s[i]
	struct btval		 key, data;
	if (src_index == 0 && IS_BRANCH(src_page)) {
		/* must find the lowest key below src_page
		 */
		rc = btree_search_first_leaf_key(bt,src_page,&key);
		if(rc!=BT_SUCCESS)
			return rc;
	} else {
		key.size = srcnode->ksize;
		key.data = NODEKEY(srcnode);
	}
	
	data.size = NODEDSZ(srcnode);
	data.data = NODEDATA(srcnode);
	if(dst_index==0 && IS_BRANCH(dst_page)){
		struct btval restored_key;
		rc = btree_search_first_leaf_key(bt,dst_page,&restored_key);
		if(rc!=BT_SUCCESS)
			return rc;
		if (btree_update_key(dst_page, 0, &restored_key) != BT_SUCCESS)
			return BT_FAIL;
	}
	rc = btree_insert_node(bt, dst_page, dst_index, &key, &data, NODEPGNO(srcnode),srcnode->flags);
	if (rc != BT_SUCCESS)
		return rc;

	/* Delete the node from the source page.
	 */
	__btree_del_node(src_page, src_index);

	/* Update the parent separators.
	 */
	/*			   3   6     9 
	  src page  2  3 4   6 7    9 10
	*/
	if (src_index == 0 && src_page->parent_index != 0) {
		
		struct node * new_src_node=NODEPTR(src_page,0);
		struct btval key ={.size=new_src_node->ksize, .data=new_src_node->data};

		//DPRINTF("update separator for source page %u to [%.*s]",src_page->pgno, (int)key.size, (char *)key.data);
		if (btree_update_key(src_page->parent, src_page->parent_index, &key) != BT_SUCCESS)
			return BT_FAIL;
	}

	if (src_index == 0 && IS_BRANCH(src_page)) {
		struct btval	 nullkey;
		nullkey.size = 0;
		assert(btree_update_key(src_page, 0, &nullkey) == BT_SUCCESS);
	}

	if (dst_index == 0 && dst_page->parent_index != 0) {
		struct node * new_dst_node=NODEPTR(dst_page,0);
		struct btval key = {.size = new_dst_node->ksize,.data = NODEKEY(new_dst_node)};

		//DPRINTF("update separator for destination page %u to [%.*s]",dst_page->pgno, (int)key.size, (char *)key.data);
		if (btree_update_key(dst_page->parent, dst_page->parent_index,&key) != BT_SUCCESS)
			return BT_FAIL;
	}

	if (dst_index == 0 && IS_BRANCH(dst_page)) {
		struct btval	 nullkey;
		nullkey.size = 0;
		assert(btree_update_key(dst_page, 0, &nullkey) == BT_SUCCESS);
	}
	bt->stat.move++;

	return BT_SUCCESS;
}

static int btree_merge(struct btree *bt, const struct mpage *src, struct mpage *dst)
{

	DPRINTF("merging page %u to %u", src->pgno, dst->pgno);

	assert(src->parent);	/* can't merge root page */
	assert(dst->parent);
	assert(src->parent==dst->parent);
	assert(bt->txn != NULL);
	assert(src->page->flags==dst->page->flags);

	/* Mark src and dst as dirty. */
	if (/*(src = mpage_copy_on_write(bt, src)) == NULL ||*/ (dst = mpage_copy_on_write(bt, dst)) == NULL)
		return BT_FAIL;

	/* Move all nodes from src to dst.
	 */
	int			 rc;
	struct node		*srcnode;
	struct btval	key, data;

	const unsigned int n = get_page_keys_count(src->page);
	for (indx_t i = 0; i < n; i++) {
		srcnode = get_node_n(src->page, i);

		/* If branch node 0 (implicit key), find the real key.
		 */
		if (i == 0 && IS_BRANCH(src)) {
			assert(srcnode->ksize==0);
			/* must find the lowest key below src
			 */
			rc= btree_search_first_leaf_key(bt, src, &key);
			if(rc != BT_SUCCESS) return rc;
		
			DPRINTF("found lowest leaf key [%.*s]",(int)key.size, (char*)key.data);

		} else {
			key.size = srcnode->ksize;
			key.data = (char*)srcnode->data;
		}

		
		data.size = NODEDSZ(srcnode);
		data.data = NODEDATA(srcnode);
		rc = btree_insert_node(bt, dst, NUMKEYS(dst), &key, &data, NODEPGNO(srcnode), srcnode->flags);
		if (rc != BT_SUCCESS)
			return rc;
	}

	DPRINTF("dst page %u now has %lu keys (%.1f%% filled)",dst->pgno, NUMKEYS(dst), (float)PAGEFILL(bt, dst) / 10);

	/* Unlink the src page from parent.
	 */
	__btree_del_node(src->parent, src->parent_index);
	assert(src->parent_index>0);

	if (IS_LEAF(src))
		bt->meta.leaf_pages--;
	else
		bt->meta.branch_pages--;
	bt->stat.merge++;
	return btree_rebalance(bt, src->parent);
}

#define FILL_THRESHOLD	 250

static inline unsigned int get_page_fill(struct btree * bt,struct mpage * mp){
	const unsigned int left_size=mp->page->upper - mp->page->lower;
	const unsigned int page_fill = 1000*(bt->head.psize-offsetof(struct page,offsets)-left_size)/(bt->head.psize-offsetof(struct page,offsets));
	return page_fill;
}
static int btree_rebalance(struct btree *bt, struct mpage *mp)
{
	struct mpage	*root;
	assert(bt != NULL);
	assert(bt->txn != NULL);
	assert(mp != NULL);
	const unsigned int page_fill =get_page_fill(bt,mp);

	if (page_fill >= FILL_THRESHOLD) {
	//	DPRINTF("no need to rebalance page %u, %u%%above fill threshold",mp->pgno, page_fill);
		return BT_SUCCESS;
	}
	DPRINTF("rebalancing %s page %u (has %lu keys, %.1f%% full)", IS_LEAF(mp) ? "leaf" : "branch",
	    mp->pgno, NUMKEYS(mp), (float)PAGEFILL(bt, mp) / 10);

	struct mpage	* const parent_page = mp->parent;

	if (parent_page == NULL) {//root
		const unsigned int keys = get_page_keys_count(mp->page);
		if (keys == 0) {
			DPRINTF("tree is completely empty");
			bt->txn->root = P_INVALID;
			bt->meta.depth--;
			bt->meta.leaf_pages--;
			assert(IS_LEAF(mp));
		} else if (IS_BRANCH(mp) && keys == 1) {
			DPRINTF("collapsing root page!");
			bt->txn->root = get_node_n(mp->page,0)->p.np_pgno;//NODEPGNO(NODEPTR(mp, 0));
			if ((root = btree_get_mpage(bt, bt->txn->root)) == NULL)
				return BT_FAIL;
			root->parent = NULL;
			bt->meta.depth--;
			bt->meta.branch_pages--;
		} else
			;//DPRINTF("root page doesn't need rebalancing");
		return BT_SUCCESS;
	}

	/* The parent_page (branch page) must have at least 2 pointers,
	 * otherwise the tree is invalid.
	 */
	assert(NUMKEYS(parent_page) > 1);

	/* Leaf page fill factor is below the threshold.
	 * Try to move keys from left or right neighbor, or
	 * merge with a neighbor page.
	 */

/*			   	   3    6     9 
	  src page  2  3 4   6 7    9 10
	*/
	if (mp->parent_index == 0) {//leftmost, merge <
		/* We're the leftmost leaf in our parent_page.
		 */
		DPRINTF("reading right neighbor");
		struct mpage * const right_mpage=get_right_sibling_mpage(bt,mp);
		if(!right_mpage) return BT_FAIL;

		DPRINTF("found right page %u (%lu keys, %.1f%% full)",right_mpage->pgno, NUMKEYS(right_mpage), (float)PAGEFILL(bt, right_mpage) / 10);
		if (PAGEFILL(bt, right_mpage) >= FILL_THRESHOLD && NUMKEYS(right_mpage) >= 2)
			//src->dst
			return btree_move_node(bt, right_mpage,  mp, true);
		else { /* FIXME: if (has_enough_room()) */
				return btree_merge(bt, right_mpage, mp);
			}
	} else {
		/* There is at least one neighbor to the left.
		 */
		struct mpage	* const left_mpage=get_left_sibling_mpage(bt,mp);
		if(!left_mpage) return BT_FAIL;
		
		DPRINTF("found left page %u (%lu keys, %.1f%% full)",left_mpage->pgno, NUMKEYS(left_mpage), (float)PAGEFILL(bt, left_mpage) / 10);
		/* If the neighbor page is above threshold and has at least two
		 * keys, move one key from it.
		 *
		 * Otherwise we should try to merge them
		 */
		if (PAGEFILL(bt, left_mpage) >= FILL_THRESHOLD && NUMKEYS(left_mpage) >= 2){
				const unsigned int si = NUMKEYS(left_mpage) - 1;
				return btree_move_node(bt, left_mpage,  mp, false);//move right
			}else { /* FIXME: if (has_enough_room()) */
				return btree_merge(bt, mp, left_mpage);
			}
	}


}

int btree_txn_del(struct btree_txn *txn,struct btval *key)
{
	int		 rc, exact, close_txn = 0;
	unsigned int	 ki;
	struct node	*leaf;
	struct mpage	*mp;

	DPRINTF("========> delete key %.*s", (int)key->size, (char *)key->data);

	assert(key != NULL);
	assert(txn);
	struct btree*  bt = txn->bt;

	if (F_ISSET(txn->flags, BT_TXN_RDONLY)) {
		errno = EINVAL;
		return BT_FAIL;
	}

	if (key->size == 0 || key->size > MAXKEYSIZE) {
		errno = EINVAL;
		return BT_FAIL;
	}

	if ((rc = btree_search_leaf_page(txn->bt, txn, key, NULL, 1, &mp)) != BT_SUCCESS)
		goto done;

	leaf = btree_search_in_leaf_page(txn->bt, mp, key, &exact, &ki);
	if (leaf == NULL || !exact) {
		errno = ENOENT;
		rc = BT_FAIL;
		goto done;
	}

	__btree_del_node(mp, ki);
	bt->meta.entries--;
	rc = btree_rebalance(bt, mp);


done:
	if (rc != BT_SUCCESS)
		txn->flags |= BT_TXN_ERROR;
	mpage_prune(bt);
	return rc;
}
/* Split page <*mpp>, and insert <key,(data|newpgno)> in either left or
 * right sibling, at index <*newindxp> (as if unsplit). Updates *mpp and
 * *newindxp with the actual values after split, ie if *mpp and *newindxp
 * refer to a node in the new right sibling page.
 */
static int btree_split_insert(struct btree *bt, struct mpage **mpp, unsigned int *newindxp,const struct btval *newkey, const struct btval *newdata, pgno_t newpgno)
{
	int		 rc = BT_SUCCESS;
	assert(bt != NULL);
	assert(bt->txn != NULL);

	struct mpage * const mp = *mpp;
	const indx_t		 new_index = *newindxp;
	const unsigned int n = get_page_keys_count(mp->page);
	assert(new_index>=0 && new_index<=n);//it is appending if new_index==n
	DPRINTF("-----> splitting %s page %u and adding [%.*s] at index %i/%u",IS_LEAF(mp) ? "leaf" : "branch", mp->pgno,(int)newkey->size, (char *)newkey->data, *newindxp, n-1);

	if (mp->parent == NULL) {
		struct mpage* const root_mpage = new_root_page(bt->txn);
		if(root_mpage==NULL)
			return BT_FAIL;
		mp->parent=root_mpage;
		mp->parent_index = 0;

		/* Add left (implicit) pointer. */
		if (btree_insert_branch_node(bt, root_mpage, 0, NULL, mp->pgno) != BT_SUCCESS)
			return BT_FAIL;
	} 
	/* Create a right sibling. */
	struct mpage	*const pright = btree_new_page(bt, mp->page->flags);
	if (pright == NULL)
		return BT_FAIL;
	pright->parent = mp->parent;
	pright->parent_index = mp->parent_index + 1;
	DPRINTF("new right sibling: page %u", pright->pgno);

	const unsigned int split_indx = get_page_keys_count(mp->page)/ 2 + 1;
	assert(get_page_keys_count(mp->page)>2);

	/* First find the separating key between the split pages.
	 */
	//k0 k1 k2 new k3
	struct btval	 sep_key;	memset(&sep_key, 0, sizeof(sep_key));
	if (new_index == split_indx) {
		sep_key.size = newkey->size;
		sep_key.data = newkey->data;
		struct node	*node = get_node_n(mp->page, split_indx);
		if(!bt->cmp){
				struct btval next_key;
				next_key.size=node->ksize;
				next_key.data=node->data;
				assert(bt_cmp(bt,&next_key,&sep_key)>0);
			}
		
	} else {
		struct node	*node = get_node_n(mp->page, split_indx);
		sep_key.size = node->ksize;
		sep_key.data = NODEKEY(node);
	}

	DPRINTF("sep key is [%.*s],new_index:%u,split_indx:%u,", (int)sep_key.size, (char *)sep_key.data,new_index,split_indx);

	/* Copy separator key to the parent.
	 */
	assert(pright->parent==mp->parent);
	if (SIZELEFT(mp->parent) < bt_branch_size(bt, &sep_key)) {
		rc = btree_split_insert(bt, &pright->parent, &pright->parent_index,&sep_key, NULL, pright->pgno);

		/* Right page might now have changed parent.
		 * Check if left page also changed parent.
		 */
		if (pright->parent != mp->parent &&mp->parent_index >= NUMKEYS(mp->parent)) {
			mp->parent = pright->parent;
			mp->parent_index = pright->parent_index - 1;
		}
	} else {
		assert(pright->parent_index>0);
		rc = btree_insert_branch_node(bt, mp->parent, pright->parent_index,&sep_key, pright->pgno);
	}
	if (rc != BT_SUCCESS) {
		return BT_FAIL;
	}

/* Move half of the keys to the right sibling. */
	uint8_t		 flags=0;
	pgno_t		 pgno = 0;
	struct page	*copy;
	if ((copy = malloc(bt->head.psize)) == NULL)
		return BT_FAIL;
	memcpy(copy, mp->page, bt->head.psize);
	assert(mp->ref == 0);				/* XXX */
	memset(&mp->page->offsets, 0, bt->head.psize - PAGEHDRSZ);
	mp->page->lower = PAGEHDRSZ;
	mp->page->upper = bt->head.psize;

	
	struct btval	  rkey, rdata;
	unsigned int	 i, j;
	//split, k0 k1 k2 k3 new k4 k5 k6
	assert(n==get_page_keys_count(copy));
	bool insert_new=false;
	//this is a hard loop and the only way to do it!
	for(i=0,j=0;;){
			struct mpage* const p= i<split_indx ? mp: pright;
			if(i==split_indx){
				j= i==new_index && insert_new;//hit split_index again!
			}
			if(i==new_index&&!insert_new){
				rkey=*newkey;
				if(IS_LEAF(p)){
					rdata=*newdata;
				}else
					pgno=newpgno;
				flags=0;
				*newindxp=j;
				*mpp=p;
				insert_new=true;
			}else if(i==n){
				break;
			}else {
				struct node* node = get_node_n(copy,i++);//NODEPTRP(copy, i);
				rkey.data = NODEKEY(node);
				rkey.size = node->ksize;
				if (IS_LEAF(p)) {
					rdata.data = NODEDATA(node);
					rdata.size = node->p.np_dsize;
				} else
					pgno = node->n_pgno;
				flags = node->flags;
			}
			if(j==0 && IS_BRANCH(p)){
				rkey.size=0; /* First branch index doesn't need key data. */
			}
			if(IS_BRANCH(p)){
				rc = btree_insert_node(bt, p, j++, &rkey, NULL, pgno,0);
			}else{
				assert(rdata.size);
				rc = btree_insert_node(bt, p, j++, &rkey, &rdata, 0,flags);
			}
		
			if(rc!=BT_SUCCESS){
				free(copy);
				return rc;
			}
	}
	assert(insert_new);
	assert(i==n);
	bt->stat.split++;
	free(copy);
	return rc;
}

int btree_txn_put(struct btree_txn *txn,struct btval *key, struct btval *data, unsigned int flags)
{
	int		 rc = BT_SUCCESS, exact;
	unsigned int	 ki;
	struct node	*leaf;
	struct mpage	*mp;
	assert(txn);
	assert(key != NULL);
	assert(data != NULL);

	if ( F_ISSET(txn->flags, BT_TXN_RDONLY)) {
		errno = EINVAL;
		return BT_FAIL;
	}

	struct btree* const bt = txn->bt;

	if (key->size == 0 || key->size > MAXKEYSIZE) {
		errno = EINVAL;
		return BT_FAIL;
	}

	DPRINTF("==> put key %.*s, size %zu, data size %zu",(int)key->size, (char *)key->data, key->size, data->size);

	rc = btree_search_leaf_page(bt, txn, key, NULL, 1, &mp);
	if (rc == BT_SUCCESS) {
		leaf = btree_search_in_leaf_page(bt, mp, key, &exact, &ki);
		if (leaf && exact) {
			if (F_ISSET(flags, BT_NOOVERWRITE)) {
				DPRINTF("duplicate key %.*s",
				    (int)key->size, (char *)key->data);
				errno = EEXIST;
				rc = BT_FAIL;
				goto done;
			}
			__btree_del_node(mp, ki);
			bt->meta.entries--;
		}
		if (leaf == NULL) {		/* append if not found */
			ki = NUMKEYS(mp);
			//DPRINTF("appending key at index %i", ki);
		}
	} else if (errno == ENOENT) {
		/* new file, just write a root leaf page */
		
		if ((mp = new_root_page(bt->txn)) == NULL) {
			rc = BT_FAIL;
			goto done;
		}
		ki = 0;
	}
	else
		goto done;

	assert(IS_LEAF(mp));
	//DPRINTF("insert new key at index %i/%u",  ki,NUMKEYS(mp)-1);

	const indx_t left_size=get_page_left_size(mp->page);
	if (  left_size < bt_leaf_size(bt, key, data)) {
		rc = btree_split_insert(bt, &mp, &ki, key, data, P_INVALID);
	} else {
		/* There is room already in this leaf page. */
		rc = btree_insert_new_leaf_node(bt, mp, ki, key, data);
	}

	if (rc != BT_SUCCESS)
		txn->flags |= BT_TXN_ERROR;
	else
		bt->meta.entries++;

done:

	mpage_prune(bt);
	return rc;
}

static pgno_t btree_compact_tree(struct btree *bt, pgno_t pgno, struct btree *btc)
{
	ssize_t		 rc;
	indx_t		 i;
	pgno_t		next;
	struct node	*node;
	struct page	*copy;
	struct mpage	*mp;

	/* Get the page and make a copy of it.
	 */
	if ((mp = btree_get_mpage(bt, pgno)) == NULL)
		return P_INVALID;
	if ((copy = malloc(bt->head.psize)) == NULL)
		return P_INVALID;
	memcpy(copy, mp->page, bt->head.psize);

        /* Go through all nodes in the (copied) page and update the
         * page pointers.
	 */
	if (F_ISSET(copy->flags, P_BRANCH)) {
		for (i = 0; i < NUMKEYSP(copy); i++) {
			node = NODEPTRP(copy, i);
			node->n_pgno = btree_compact_tree(bt, node->n_pgno, btc);
			if (node->n_pgno == P_INVALID) {
				free(copy);
				return P_INVALID;
			}
		}
	} else if (F_ISSET(copy->flags, P_LEAF)) {
		for (i = 0; i < NUMKEYSP(copy); i++) {
			node = NODEPTRP(copy, i);
			if (F_ISSET(node->flags, F_BIGDATA)) {
				//memcpy(&next, NODEDATA(node), sizeof(next));
				next = *(pgno_t*)NODEDATA(node);
				const pgno_t new_page_no = btree_compact_tree(bt, next, btc);
				if (new_page_no == P_INVALID) {
					free(copy);
					return P_INVALID;
				}
				*(pgno_t*)NODEDATA(node)=new_page_no;
				//memcpy(NODEDATA(node), &next, sizeof(next));
			}
		}
	} else if (F_ISSET(copy->flags, P_OVERFLOW)) {
	
		if (copy->p_next_pgno > 0) {
			copy->p_next_pgno = btree_compact_tree(bt, copy->p_next_pgno, btc);
			if (copy->p_next_pgno == P_INVALID) {
				free(copy);
				return P_INVALID;
			}
		}
	} else
		assert(0);

	copy->pgno = btc->txn->next_pgno++;
	rc = write(btc->fd, copy, bt->head.psize);
	const pgno_t new_page_no=copy->pgno;
	free(copy);copy=NULL;
	if (rc != (ssize_t)bt->head.psize)
		return P_INVALID;
	mpage_prune(bt);
	return new_page_no ;
}

int btree_compact(struct btree *bt)
{
	char			*compact_path = NULL;

	struct btree_txn	*txn, *txnc = NULL;
	
	pgno_t			 root;

	assert(bt != NULL);

	DPRINTF("compacting btree %p with path %s", bt, bt->path);

	if (bt->path == NULL) {
		errno = EINVAL;
		return BT_FAIL;
	}

	if ((txn = btree_txn_begin(bt, 0)) == NULL)
		return BT_FAIL;

	if (asprintf(&compact_path, "%s.compact.XXXXXX.db", bt->path) == -1) {
		btree_txn_abort(txn);
		return BT_FAIL;
	}
	printf("%s\n",compact_path);
	int			 fd = mkstemps(compact_path,3);
	if (fd == -1) {
		free(compact_path);
		btree_txn_abort(txn);
		return BT_FAIL;
	}
	struct btree		*btc;
	if ((btc = btree_open_fd(fd, 0)) == NULL)
		goto failed;
	memcpy(&btc->meta, &bt->meta, sizeof(bt->meta));
	btc->meta.revisions = 0;
	btc->meta.prev_meta=0;

	if ((txnc = btree_txn_begin(btc, 0)) == NULL)
		goto failed;

	if (bt->meta.root != P_INVALID) {
		root = btree_compact_tree(bt, bt->meta.root, btc);
		if (root == P_INVALID)
			goto failed;
		if (btree_write_meta(btc, root,0) != BT_SUCCESS)
			goto failed;
	}

	fsync(fd);

	DPRINTF("renaming %s to %s", compact_path, bt->path);
	if (rename(compact_path, bt->path) != 0)
		goto failed;

	/* Write a "tombstone" meta page so other processes can pick up
	 * the change and re-open the file.
	 */
	if (btree_write_meta(bt, P_INVALID,BT_TOMBSTONE) != BT_SUCCESS)
		goto failed;

	btree_txn_abort(txn);
	btree_txn_abort(txnc);
	free(compact_path);
	btree_close(btc);
	mpage_prune(bt);
	return 0;

failed:
	btree_txn_abort(txn);
	btree_txn_abort(txnc);
	unlink(compact_path);
	free(compact_path);
	btree_close(btc);
	mpage_prune(bt);
	return BT_FAIL;
}

/* Reverts the last change. Truncates the file at the last root page.
 */
int btree_revert(struct btree *bt)
{
	if (btree_read_meta(bt, NULL) != 0)
		return -1;

	DPRINTF("truncating file at page %u", bt->meta.root);
	return ftruncate(bt->fd, bt->head.psize * bt->meta.root);
}

void
btree_set_cache_size(struct btree *bt, unsigned int cache_size)
{
	bt->stat.max_cache = cache_size;
}

unsigned int
btree_get_flags(struct btree *bt)
{
	return (bt->flags & ~BT_FIXPADDING);
}

const char *
btree_get_path(struct btree *bt)
{
	return bt->path;
}

const struct btree_stat * btree_stat(struct btree *bt)
{
	if (bt == NULL)
		return NULL;

	bt->stat.branch_pages = bt->meta.branch_pages;
	bt->stat.leaf_pages = bt->meta.leaf_pages;
	bt->stat.overflow_pages = bt->meta.overflow_pages;
	bt->stat.revisions = bt->meta.revisions;
	bt->stat.depth = bt->meta.depth;
	bt->stat.entries = bt->meta.entries;
	bt->stat.psize = bt->head.psize;
	bt->stat.created_at = bt->meta.created_at;
	bt->stat.meta=bt->meta_pgno;
	bt->stat.root=bt->meta.root;
	bt->stat.prev_meta=bt->meta.prev_meta;

	return &bt->stat;
}

void print_node(int is_data,const struct node * node){
	if(is_data){
		if(node->flags&F_BIGDATA){

		}else{
			const char * data = (char*)node->data + node->ksize;
			printf("%.*s:%.*s ",node->ksize,node->data,node->p.np_dsize,data );
		}
	}else{
		printf("%.*s > %u ",node->ksize,node->data,node->p.np_pgno );
	}
}
static inline unsigned int page_fill(const struct btree * bt, const struct page * page){
	const unsigned int header_sz= offsetof(struct page, offsets);
	const unsigned int left_size = page->upper-page->lower;
	return 1000 * (bt->head.psize - header_sz - left_size) / (bt->head.psize - header_sz);
}
void print_hex_array(const char *array, size_t length) {
    for (size_t i = 0; i < length; i++) {
        printf("%02x", (unsigned char)array[i]);
        if (i < length - 1) {
        }
    }
    printf("\n");
}
void 		btree_dump_page(struct btree *bt, unsigned int page_no)
{
	struct page * page = malloc(bt->head.psize);

	if (__btree_read_page(bt, page_no, page) != BT_SUCCESS) {
		free(page);
		return ;
	}
	if(page->flags & P_LEAF){
		const unsigned int n = (page->lower- offsetof(struct page,offsets))>>1;
		const unsigned int left_size= page->upper - page->lower;
		printf("n=%u,left_size=%u, page_fill:%u%%\n",n,left_size,page_fill(bt,page)/10);
		for(unsigned int k=0;k<n;++k){
			struct node * node =  (struct node*)((char*)page+page->offsets[k]);
			print_node(1,node);
		}
		printf("\n");

	}else if(page->flags & P_BRANCH){
		const unsigned int n = (page->lower- offsetof(struct page,offsets))>>1;
		const unsigned int left_size= page->upper - page->lower;
		printf("n=%u,left_size=%u, page_fill:%u%%\n",n,left_size,page_fill(bt,page)/10);
		for(unsigned int k=0;k<n;++k){
			struct node * node =  (struct node*)((char*)page+page->offsets[k]);
			print_node(0,node);
		}
		printf("\n");

	}else if(page->flags&P_OVERFLOW){

	}else if(page->flags&P_HEAD){

	}else if(page->flags&P_META){
		const struct bt_meta meta= *(struct bt_meta*)((char*)page+ offsetof(struct page,offsets));
		const size_t created_at= bt->meta.created_at;
		printf("timestamp: %s", ctime(&created_at));
		printf("depth: %u\n", meta.depth);
		printf("entries: %lu\n", meta.entries);
		printf("revisions: %u\n", meta.revisions);
		printf("root: %u\n", meta.root);
		printf("branch pages: %u\n", meta.branch_pages);
		printf("leaf pages: %u\n", meta.leaf_pages);
		printf("overflow pages: %u\n", meta.overflow_pages);
		
		printf("previous meta page: %u\n", meta.prev_meta);
		print_hex_array(meta.hash,sizeof(meta.hash));


	}
	free(page);
}