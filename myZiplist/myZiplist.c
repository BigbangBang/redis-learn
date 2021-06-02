#include "./myZiplist.h"

#define redis_unreachable abort

#define ZIP_END 255
#define ZIP_BIG_PREVLEN 254

// 计算机都是小端
#define memrev16ifbe(p) ((void)(0))
#define memrev32ifbe(p) ((void)(0))
#define memrev64ifbe(p) ((void)(0))
#define intrev16ifbe(v) (v)
#define intrev32ifbe(v) (v)
#define intrev64ifbe(v) (v)


// <zlbytes> <zltail> <zllen> <entry> <entry> ... <entry> <zlend>

#define ZIP_STR_MASK 0xc0
#define ZIP_INT_MASK 0x30
#define ZIP_STR_06B (0 << 6)
#define ZIP_STR_14B (1 << 6)
#define ZIP_STR_32B (2 << 6)
#define ZIP_INT_16B (0xc0 | 0 << 4)
#define ZIP_INT_32B (0xc0 | 1 << 4)
#define ZIP_INT_64B (0xc0 | 2 << 4)
#define ZIP_INT_24B (0xc0 | 3 << 4)
#define ZIP_INT_8B 0xfe

#define ZIP_INT_IMM_MASK 0x0f

#define ZIP_INT_IMM_MIN 0xf1
#define ZIP_INT_IMM_MAX 0xfd

#define INT24_MAX 0x7fffff
#define INT24_MIN (-INT24_MAX - 1)

// 是否是字符串类型节点
#define ZIP_IS_STR(enc) (((enc) & ZIP_STR_MASK) < ZIP_STR_MASK)
// ziplist占用字节数
#define ZIPLIST_BYTES(zl) (*((uint32_t)(zl)))
// 获取最后一个节点地址
#define ZIPLIST_TAIL_OFFSET(zl) (*((uint32_t*)((zl)+sizeof(uint32_t))))
// 获取压缩列表的长度
#define ZIPLIST_LENGTH(zl)      (*((uint16_t*)((zl)+sizeof(uint32_t)*2)))
// 压缩类表头的长度 
#define ZIPLIST_HEADER_SIZE (sizeof(uint32_t)*2+sizeof(uint16_t))
// 尾部的长度
#define ZIPLIST_END_SIZE (sizeof(uint_8))
// 首个节点的位置
#define ZIPLIST_ENTRY_HAED(zl) (zl+ZIPLIST_HEADER_SIZE)
//指向最后一个节点的指针 
#define ZIPLIST_ENTRY_TAIL(zl) ((zl)+intrev32ifbe(ZIPLIST_TAIL_OFFSET(zl)))
//指向ziplist最后一个字节的指针
#define ZIPLIST_ENTRY_END(zl) ((zl)+intrev32ifbe(ZIPLIST_BYTES(zl))-1)

//增加压缩列表的长度
#define ZIPLIST_INCE_LENGTH(zl, ince){ \
    if (ZIPLIST_LENGTH(zl) < UINT16_MAX) \
        ZIPLIST_LENGTH(zl) = intrev16ifbe(intrev16ifbe(ZIPLIST_LENGTH(zl))+incr); \
}

//表示节点的数据结构
typedef struct zlentry {
    unsigned int prevrawlensize;  //1个字节或者5个字节
    unsigned int prevrawlen;      //前置节点的长度
    unsigned int lensize; 
    unsigned int len;
    unsigned int headersize;
    unsigned char encoding;

    unsigned char *p; 

} zlentry;

#define ZIPLIST_ENTRY_ZERO(zle) { \
    (zle)->prevrawlensize = (zle)->prevrawlen = 0; \
    (zle)->lensize = (zle)->len = (zle)->headersize = 0; \
    (zle)->encoding = 0; \
    (zle)->p = NULL; \
}

#define ZIP_ENTRY_ENCODING(ptr, encoding) do {  \
    (encoding) = ((ptr)[0]); \
    if ((encoding) < ZIP_STR_MASK) (encoding) &= ZIP_STR_MASK; \
} while(0)

//节点编码长度
#define ZIP_ENCODING_SIZE_INVALID 0xff
static inline unsigned int zipEncodingLenSize(unsigned char encoding) {
    if (encoding == ZIP_INT_16B || encoding == ZIP_INT_32B ||
        encoding == ZIP_INT_24B || encoding == ZIP_INT_64B ||
        encoding == ZIP_INT_8B)
        return 1;
    if (encoding >= ZIP_INT_IMM_MIN && encoding <= ZIP_INT_IMM_MAX)
        return 1;
    if (encoding == ZIP_STR_06B)
        return 1;
    if (encoding == ZIP_STR_14B)
        return 2;
    if (encoding == ZIP_STR_32B)
        return 5;
    return ZIP_ENCODING_SIZE_INVALID;
}

#define ZIP_ASSERT_ENCODING(encoding) do {                                     \
    assert(zipEncodingLenSize(encoding) != ZIP_ENCODING_SIZE_INVALID);         \
} while (0)


// 返回存储编码需要的字节
static inline unsigned int zipIntSize(unsigned char encoding) {
    switch(encoding) {
    case ZIP_INT_8B:  return 1;
    case ZIP_INT_16B: return 2;
    case ZIP_INT_24B: return 3;
    case ZIP_INT_32B: return 4;
    case ZIP_INT_64B: return 8;
    }
    if (encoding >= ZIP_INT_IMM_MIN && encoding <= ZIP_INT_IMM_MAX)
        return 0; /* 4 bit immediate */
    
    redis_unreachable();
    return 0;
}


// 在指针p执行的位置，存储encoding信息
unsigned int zipStoreEntryEncoding(unsigned char *p, unsigned char encoding, unsigned int rawlen){
    unsigned char len = 1, buf[5];

    if(ZIP_IS_STR(encoding)) {
        if(rawlen <= 0x3f) {
            if(!p) return len;
            buf[0] = ZIP_STR_06B | rawlen;
        } else if(rawlen <= 0x3fff) {
            len += 1;
            if(!p) return len;
            buf[0] = ZIP_STR_14B | ((rawlen >> 8) & 0x3f);
            buf[1] = rawlen & 0xff;
        } else {
            len += 4;
            if(!p) return len;
            buf[0] = ZIP_STR_32B;
            buf[1] = (rawlen >> 24) & 0xff;
            buf[2] = (rawlen >> 16) & 0xff;
            buf[3] = (rawlen >> 8) & 0xff;
            buf[4] = rawlen & 0xff;
        }
    }else {
        if(!p) return len;
        buf[0] = encoding;
    }

    memcpy(p, buf, len);
    return len;
}



