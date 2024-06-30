/*	$OpenBSD: btest.c,v 1.1 2010/05/31 17:36:31 martinh Exp $ */

/* Simple test program for the btree database. */
/*
 * Copyright (c) 2009 Martin Hedenfalk <martin@bzero.se>
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

#include <sys/types.h>

#include <err.h>
#include <getopt.h>
#include <stdio.h>
#include <string.h>

#include "btree.h"
#include <assert.h>
#include <time.h>
#include <unistd.h>
#include <stdint.h>
#include <stdlib.h>
uint64_t get_cur_us() {
      struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000000 + ts.tv_nsec / 1000;
}
void dump_stat(struct btree* bt){
const struct btree_stat * const i= btree_stat(bt);
		const size_t created_at= i->created_at;
		printf("timestamp: %s", ctime(&created_at));
		printf("depth: %u\n", i->depth);
		printf("entries: %llu\n", i->entries);
		printf("revisions: %u\n", i->revisions);
		printf("branch pages: %u\n", i->branch_pages);
		printf("leaf pages: %u\n", i->leaf_pages);
		printf("overflow pages: %u\n", i->overflow_pages);
		printf("cache_size: %u\n", i->cache_size);
		printf("max_cache: %u\n", i->max_cache);
		printf("hits: %llu\n", i->hits);
		printf("misses: %llu\n", i->misses);
		printf("reads: %llu\n", i->reads);
		printf("writes: %llu\n", i->writes);
		printf("fsyncs: %llu\n", i->fsyncs);
		printf("meta: %u\n", i->meta);
		printf("prev_meta: %u\n", i->prev_meta);
		printf("root: %u\n", i->root);
		printf("split: %lu\n", i->split);
		printf("merge: %lu\n", i->merge);
		printf("move: %lu\n", i->move);
}
int main(int argc, char **argv)
{
	int		 c, rc = BT_FAIL;
	unsigned int	 flags = 0;
	
	struct cursor	*cursor;
	const char	*filename = "test.db";
	struct btval	 key, data, maxkey;

	while ((c = getopt(argc, argv, "nrf:")) != -1) {
		switch (c) {
		case 'r':
			flags |= BT_REVERSEKEY;
			break;
		case 'n':
			flags |= BT_NOSYNC;
			break;
		case 'f':
			filename = optarg;
			break;
		}
	}

	argc -= optind;
	argv += optind;

	if (argc == 0)
		errx(1, "missing command");

	struct btree	*bt = btree_open(filename, flags, 0644);
	if (bt == NULL)
		err(1,"fail to open %s", filename);

	memset(&key, 0,sizeof(key));
	memset(&data,0, sizeof(data));
	memset(&maxkey,0, sizeof(maxkey));

	if (strcmp(argv[0], "info") == 0) {
		dump_stat(bt);
	}
	else if (strcmp(argv[0], "put") == 0) {
		if (argc < 3)
			errx(1, "missing arguments");
		const uint64_t st=get_cur_us();
		key.data = argv[1];
		key.size = strlen(key.data);
		data.data = argv[2];
		data.size = strlen(data.data);
		struct btree_txn	* txn=btree_txn_begin(bt,0);

		rc = btree_txn_put(txn, &key, &data, 0);

		btree_txn_commit(txn);
		const uint64_t et=get_cur_us();
		printf("put %lu us\n", et-st);
		if (rc == BT_SUCCESS)
			printf("OK\n");
		else
			printf("FAIL\n");
		dump_stat(bt);
	}else	if (strcmp(argv[0], "putn") == 0) {
		if (argc < 4)
			errx(1, "missing arguments");
		int n =atoi(argv[3]);
		const uint64_t st=get_cur_us();
	
		
		char  buf_key[1024];
		char buf_val[1024];
		const unsigned int B=10240;
		for(unsigned int rest=n,i=0;rest>0;){
			struct btree_txn	* txn=btree_txn_begin(bt,0);
			assert(txn);
			const unsigned int r= rest<B?rest:B;
				for(int k=0;k<r;++k){
					++i;
					snprintf(buf_key, sizeof(buf_key),"%s_%d",argv[1],i);
					snprintf(buf_val, sizeof(buf_val),"%s_%d",argv[2],i);
				//	printf("%s\n",buf);
					key.data = buf_key;
					key.size = strlen(key.data);
					data.data = buf_val;
					data.size = strlen(data.data);
					assert(data.size);
					rc = btree_txn_put(txn,&key,&data,0);
					assert(rc==BT_SUCCESS);

				}
			btree_txn_commit(txn);
			rest-=r;
	}
		const uint64_t et=get_cur_us();
		printf("putn %lu us\n", et-st);
		dump_stat(bt);
		
	}
	 else if (strcmp(argv[0], "del") == 0) {
		if (argc < 1)
			errx(1, "missing argument");
		key.data = argv[1];
		key.size = strlen(key.data);
		struct btree_txn* const txn = btree_txn_begin(bt,0);
		rc = btree_txn_del(txn, &key);
		if (rc == BT_SUCCESS)
			;//printf("OK\n");
		else
			printf("FAIL\n");
		btree_txn_commit(txn);
		dump_stat(bt);
	} 	 else if (strcmp(argv[0], "dels") == 0) {
		if (argc < 3)
			errx(1, "missing argument");
		key.data = argv[1];
		key.size = strlen(key.data);
		maxkey.data = argv[2];
		maxkey.size = strlen(maxkey.data);
		struct btree_txn* const txn = btree_txn_begin(bt,0);
		cursor = btree_txn_cursor_open(txn);
		flags = BT_CURSOR;
		while ((rc = btree_cursor_get(cursor, &key, NULL,flags)) == BT_SUCCESS) {
			if ( btree_cmp(bt, &key, &maxkey) > 0)
				break;
			rc = btree_txn_del(txn, &key);
			if(rc!=BT_SUCCESS)
				printf("del %s  %.*s\n", rc == BT_SUCCESS ? "OK":"FAIL",
					(int)key.size, (char *)key.data);
			flags = BT_NEXT;
		}
		btree_cursor_close(cursor);
		btree_txn_commit(txn);
		dump_stat(bt);
	}
	else if (strcmp(argv[0], "get") == 0) {
		if (argc < 2)
			errx(1, "missing arguments");
		const uint64_t st=get_cur_us();
		key.data = argv[1];
		key.size = strlen(key.data);
		struct btree_txn* const txn = btree_txn_begin(bt,1);
		rc = btree_txn_get(txn, &key, &data);
		const uint64_t et=get_cur_us();
		printf("get %lu us\n", et-st);
		
		if (rc == BT_SUCCESS) {
			printf("OK %.*s\n", (int)data.size, (char *)data.data);
		} else {
			printf("FAIL\n");
		}
		btree_txn_abort(txn);
		dump_stat(bt);

	} else if (strcmp(argv[0], "scan") == 0) {
		if (argc > 1) {
			key.data = argv[1];
			key.size = strlen(key.data);
			flags = BT_CURSOR;
		}
		else
			flags = BT_FIRST;
		if (argc > 2) {
			maxkey.data = argv[2];
			maxkey.size = strlen(maxkey.data);
		}
		struct btree_txn* const txn = btree_txn_begin(bt,1);
		cursor = btree_txn_cursor_open(txn);
		while ((rc = btree_cursor_get(cursor, &key, &data,flags)) == BT_SUCCESS) {
			if (argc > 2 && btree_cmp(bt, &key, &maxkey) > 0)
				break;
			printf("OK  %.*s %zi\n", (int)key.size, (char *)key.data, data.size);
			flags = BT_NEXT;
		}
		btree_cursor_close(cursor);
		btree_txn_abort(txn);
		dump_stat(bt);
	}else if (strcmp(argv[0], "scan2") == 0) {
		if (argc > 1) {
			key.data = argv[1];
			key.size = strlen(key.data);
			flags = BT_CURSOR;
		}
		else
			flags = BT_FIRST;
		if (argc > 2) {
			maxkey.data = argv[2];
			maxkey.size = strlen(maxkey.data);
		}
		struct btree_txn* const txn = btree_txn_begin(bt,1);
		cursor = btree_txn_cursor_open(txn);
		for(;;)
		{	
			sleep(1);
			while ((rc = btree_cursor_get(cursor, &key, &data,flags)) == BT_SUCCESS) {
				if (argc > 2 && btree_cmp(bt, &key, &maxkey) > 0)
					break;
				printf("OK %zi %.*s\n", key.size, (int)key.size, (char *)key.data);
				flags = BT_NEXT;
				sleep(1);
			}
		}
		btree_cursor_close(cursor);
		btree_txn_abort(txn);
		dump_stat(bt);
	}  else if (strcmp(argv[0], "compact") == 0) {
		const uint64_t st=get_cur_us();
		if ((rc = btree_compact(bt)) != BT_SUCCESS)
			warn("compact");
				const uint64_t et=get_cur_us();
		printf("compact %lu us\n", et-st);
		dump_stat(bt);
	} else if (strcmp(argv[0], "revert") == 0) {
		if ((rc = btree_revert(bt)) != BT_SUCCESS)
			warn("revert");
	} else if (strcmp(argv[0], "print") == 0) {
		if (argc < 2)
			errx(1, "missing arguments");
		const unsigned int page_no = atoi(argv[1]);
		btree_dump_page(bt,page_no);
	} 
	else
		errx(1, "%s: invalid command", argv[0]);
	
	btree_close(bt);

	return rc;
}

