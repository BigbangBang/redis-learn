#ifndef MY_ZIPLIST_H
#define MY_ZIPLIST_H

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>


#define MY_ZIPLIST_HEAD 0
#define MY_ZIPLIST_TAIL 1

typedef struct {
    unsigned char *sval;
    unsigned int slen;
    long long lval;
} myZiplistEntry;

unsigned char *ziplistNew();
unsigned char *ziplistMerge(unsigned char **frist, unsigned char **second);
unsigned char *ziplistPush(unsigned char *zl, unsigned char *s, unsigned int slen, int where);
unsigned char *ziplistIndex(unsigned char *zl, unsigned char *p);
unsigned char *ziplistNext(unsigned char *zl, unsigned char *p);
unsigned char *ziplistPrev(unsigned char *zl, unsigned char *p);
unsigned int ziplistGet(unsigned char *p, unsigned char **sval, unsigned int *slen, long long *lval);
unsigned char *ziplistInsert(unsigned char *zl, unsigned char *p, unsigned char *s, unsigned int slen);
unsigned char *ziplistDelete(unsigned char *zl, unsigned char **p);
unsigned char *ziplistDeleteRange(unsigned char *zl, int index, unsigned int num);
unsigned char *ziplistReplace(unsigned char *zl, unsigned char *p, unsigned char *s, unsigned int slen);
unsigned int ziplistCompare(unsigned char *p, unsigned char *s, unsigned int slen);
unsigned char *ziplistFind(unsigned char *zl, unsigned char *p, unsigned char *vstr, unsigned int vlen, unsigned int skip);
unsigned int ziplistLen(unsigned char *zl);
size_t ziplistBlobLen(unsigned char *zl);
void ziplistRepr(unsigned char *zl);

typedef int (*ziplistValidateEntryCB)(unsigned char *p, void *userData);
int ziplistVaildateInterity(unsigned char *zl, size_t size, int deep, ziplistValidateEntryCB entry_cb, void *cb_userData);
void ziplistRandomPair(unsigned char *zl, unsigned long total_count, myZiplistEntry *key, myZiplistEntry *val);
void ziplistRandomPairs(unsigned char *zl, unsigned int count, myZiplistEntry *keys, myZiplistEntry *vals);
unsigned int ziplistRandomPairsUnique(unsigned char *zl, unsigned int count, myZiplistEntry *key, myZiplistEntry *vals);


#endif