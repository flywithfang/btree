#clear;gcc  -Werror -DDEBUG -D_GNU_SOURCE -D_XOPEN_SOURCE=500 btest.c  btree.c  sha1tiny.c  -I ./include -o ./btest
clear;gcc  -Werror -D_GNU_SOURCE -D_XOPEN_SOURCE=500 btest.c  btree.c  sha1tiny.c  -I ./include -o ./btest
