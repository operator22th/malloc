/*
 * Explicit free lists
 * 
 * Coalescing policy:
 * Deferred coalescing
 * Coalesce as you free the blocks
 * 
 * Placement policy: 
 * segregated free lists
 * Maintain list(s) of free blocks, not all blocks
 * need to store forward/back pointers, not just sizes
 * 
 * Track only free blocks, so we can use payload area
 * internal fragmentation in this way will be small
 */

#include "mm.h"

#include <string.h>

#include "memlib.h"

team_t team = {
        /* Team name */
        "Explicit free lists",
        /* First member's full name */
        "尹绍沣",
        /* First member's student ID */
        "2022012760",
        /* Second member's full name (leave blank if none) */
        "",
        /* Second member's student ID (leave blank if none) */
        ""};

#define MIN_SIZE (4 * W_SIZE)
#define ALIGNMENT D_SIZE
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~(ALIGNMENT - 1))

/* MACROS */
#define W_SIZE (sizeof(size_t))
#define D_SIZE (2 * W_SIZE)

/* UTILS */
//p为指针
#define DEREF(p) (*(size_t *)(p))
#define PACK(size, alloc) ((size) | (alloc))
#define PUT(p, val) (*(size_t *)(p) = (val))
#define MIN(x, y) ((x) < (y) ? (x) : (y))
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* BLOCK */
//hp指向header
//bp指向真正分配的内存
/* READ */
#define BLOCK_SIZE(hp) (DEREF(hp) & ~7)
#define ALLOCATED(hp) (DEREF(hp) & 1)
#define PAYLOAD(hp) ((size_t *)(hp) + 1)
#define FOOTER_P(hp) ((char *)(hp) + BLOCK_SIZE(hp) - W_SIZE)
#define HEADER_P(bp) ((size_t *)(bp) - 1)
#define PREV_ALLOCATED(hp) (DEREF(hp) & 2)
#define PREV_HEADER_P(hp) ((char *)(hp) - *((size_t *)(hp)-1))
#define NEXT_HEADER_P(hp) ((char *)(hp) + BLOCK_SIZE(hp))
#define LIST_PREV(hp) (*((void **)(hp) + 1))
#define LIST_NEXT(hp) (*((void **)(hp) + 2))

/* WRITE */
#define MARK_ALLOCATED(hp) (DEREF(hp) |= 1)
#define MARK_PREV_ALLOCATED(hp) (DEREF(hp) |= 2)
#define MARK_FREE(hp) (DEREF(hp) &= ~1)
#define CLEAR_PREV_ALLOCATED(hp) (DEREF(hp) &= ~2)
#define ENLARGE(hp, size) (DEREF(hp) += (size))

/* LIST */
#define MIN_POWER 4
#define MAX_POWER 18
#define SEG_LEN (MAX_POWER - MIN_POWER + 1)

#define LOG2(size) (8 * sizeof(long long) - __builtin_clzll((size)-1))
#define INDEX(k) ((k) < MAX_POWER ? (k)-MIN_POWER : MAX_POWER - MIN_POWER)
#define ROOT(k) ((size_t *)mem_heap_lo() + INDEX(k) * 2 - 1)


/* CONST */
#define HIGH 96
#define MIN_EXPAND_SIZE 2048

/* UTIL FUNCTIONS */

// 将hp从对应的free list中移除
static void list_remove(void *hp);
// 将hp插入到对应的free list中
static void list_insert(void *hp);
// 合并相邻的空闲块，并将合并后的块插入到对应的free list中
static void *coalesce(void *hp);
// 扩展堆空间大小，返回扩展后的块的指针
static void *extend(size_t size);
// 将hp分割成大小为size的块，higher表示是否使用高地址部分
static void *split(void *hp, size_t size, int higher);

int mm_init(void) {
    size_t end = ALIGN((size_t)mem_heap_lo() + (SEG_LEN * 2 + 1) * W_SIZE);
    if (mem_sbrk(end - (size_t)mem_heap_lo()) == (void *)-1)
        return -1;

    // 初始化每个列表的头
    int k = MIN_POWER;
    while (k <= MAX_POWER) {
        void *root = ROOT(k);
        LIST_NEXT(root) = root;
        LIST_PREV(root) = root;
        ++k;
    }

    //表示列表头的结束
    DEREF(end - W_SIZE) = 3;

    return 0;
}

void *mm_malloc(size_t size) {
    //malloc的块只用保留header，故block_size为(size + W_SIZE)
    size_t block_size = MAX(ALIGN(size + W_SIZE), MIN_SIZE);

    void *hp;
    int found = 0;

    // 寻找合适的列表
    // 在这里不进行collapse
    for (int k = MIN(LOG2(block_size), MAX_POWER); k <= MAX_POWER && !found; ++k) {
        void *root = ROOT(k);
        hp = LIST_NEXT(root);
        while (hp != root) {
            if (BLOCK_SIZE(hp) >= block_size) {
                list_remove(hp);
                found = 1;
                break;
            }
            hp = LIST_NEXT(hp);
        }
    }

    // 如果没有找到合适的块，则扩展堆空间
    if (!found) {
        size_t extend_size = block_size;
        size_t *epilogue = (size_t *)((char *)mem_heap_hi() - W_SIZE + 1);
        if ((*epilogue & 2) == 0)
            extend_size -= *(epilogue - 1);
        hp = extend(extend_size);
        if (hp == NULL)
            return NULL;
    }

    // 设置分配标记
    MARK_ALLOCATED(hp);
    MARK_PREV_ALLOCATED(NEXT_HEADER_P(hp));

    // 小的块使用低地址部分，大的块使用高地址部分
    return PAYLOAD(split(hp, block_size, block_size > HIGH));
}

void mm_free(void *ptr) {
    if (ptr == NULL)
        return;

    // coalesce会在内部处理分配标记
    void *hp = coalesce(HEADER_P(ptr));
    CLEAR_PREV_ALLOCATED(NEXT_HEADER_P(hp));
}

void *mm_realloc(void *ptr, size_t size) {
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    if (ptr == NULL)
        return mm_malloc(size);

    //malloc的块只用保留header，故block_size为(size + W_SIZE)
    size_t required_size = MAX(ALIGN(size + W_SIZE), MIN_SIZE);

    //寻找此块内存对应block的header pointer
    void *hp = HEADER_P(ptr);

    size_t coalesced_size = BLOCK_SIZE(hp);

    if(coalesced_size < required_size){
        while (1) {
            //物理上的下一个块
            void *next = NEXT_HEADER_P(hp);

            if (!ALLOCATED(next)) {
                coalesced_size += BLOCK_SIZE(next);
                list_remove(next);
            }

            //和下一块合并来装载
            if (coalesced_size >= required_size) {
                MARK_PREV_ALLOCATED(NEXT_HEADER_P(next));
                ENLARGE(hp, BLOCK_SIZE(next));
                break;
            }

            void *oldhp = hp;

            //物理上的上一个块
            if (!PREV_ALLOCATED(hp)) {
                hp = PREV_HEADER_P(hp);
                coalesced_size += BLOCK_SIZE(hp);
                list_remove(hp);
            }

            //和前后两块合并来装载
            if (coalesced_size >= required_size) {
                PUT(hp, PACK(coalesced_size, PREV_ALLOCATED(hp) | 1));
                MARK_PREV_ALLOCATED(NEXT_HEADER_P(hp));
                memmove(PAYLOAD(hp), PAYLOAD(oldhp), BLOCK_SIZE(oldhp) - W_SIZE);
                break;
            }

            //空间到现在还是不够
            PUT(hp, PACK(coalesced_size, PREV_ALLOCATED(hp) | 1));
            MARK_PREV_ALLOCATED(NEXT_HEADER_P(hp));

            // malloc 同时复制数据
            void *bp = mm_malloc(size);
            if (bp == NULL)
                return NULL;
            memcpy(bp, PAYLOAD(oldhp), BLOCK_SIZE(oldhp) - W_SIZE);

            //释放原来的块
            MARK_FREE(hp);
            PUT(FOOTER_P(hp), coalesced_size);
            CLEAR_PREV_ALLOCATED(NEXT_HEADER_P(hp));
            list_insert(hp);
            return bp;
        }
    }

    //空间够用的情况也会在此处理
    size_t free_size = BLOCK_SIZE(hp) - required_size;
    if (free_size >= MIN_SIZE) {
        PUT(hp, PACK(required_size, PREV_ALLOCATED(hp) | 1));
        void *hq = (char *)hp + required_size;
        //hq为新块的header
        PUT(hq, PACK(free_size, 2));
        PUT(FOOTER_P(hq), free_size);
        CLEAR_PREV_ALLOCATED(NEXT_HEADER_P(hq));
        list_insert(hq);
    }
    return PAYLOAD(hp);
}



// 将hp从对应的free list中移除
static void list_remove(void *hp) {
    LIST_PREV(LIST_NEXT(hp)) = LIST_PREV(hp);
    LIST_NEXT(LIST_PREV(hp)) = LIST_NEXT(hp);
}

// 将hp插入到对应的free list中
// FIFO policy 把新节点插入到链表尾部
static void list_insert(void *hp) {
    void *root = ROOT(LOG2(BLOCK_SIZE(hp)));
    void *prev = LIST_PREV(root);
    LIST_PREV(root) = hp;
    LIST_NEXT(prev) = hp;
    LIST_PREV(hp) = prev;
    LIST_NEXT(hp) = root;
}


//hp表示要分割的块的header pointer
//size表示要分割出来的块的大小
//higher表示是否使用高地址部分(低地址放小块，高地址放大块)
static void *split(void *hp, size_t size, int higher) {
    size_t free_size = BLOCK_SIZE(hp) - size;
    if (free_size >= MIN_SIZE) {
        if (higher) {
            PUT(hp, PACK(free_size, PREV_ALLOCATED(hp)));
            PUT(FOOTER_P(hp), free_size);
            list_insert(hp);
            hp = (char *)hp + free_size;

            DEREF(hp) = size | 1;
            MARK_PREV_ALLOCATED(NEXT_HEADER_P(hp));
        }
        else {
            PUT(hp, PACK(size, PREV_ALLOCATED(hp) | 1));
            void *hq = (char *)hp + size;
            PUT(hq, PACK(free_size, 2));
            PUT(FOOTER_P(hq), free_size);
            CLEAR_PREV_ALLOCATED(NEXT_HEADER_P(hq));
            list_insert(hq);
        }
    }
    return hp;
}


//合并相邻的空闲块，并将合并后的块插入到对应的free list中
//hp表示要合并的块的header pointer
static void *coalesce(void *hp) {
    void *prev = PREV_HEADER_P(hp);
    void *next = NEXT_HEADER_P(hp);
    size_t size = BLOCK_SIZE(hp); 
    int prev_alloc = PREV_ALLOCATED(hp); 
    int next_alloc = ALLOCATED(next); 

    if(!prev_alloc) {// 之前的块是空闲块
        size += BLOCK_SIZE(prev);
        list_remove(prev);
        hp = prev;
    }
    if(!next_alloc) {// 之后的块是空闲块
        size += BLOCK_SIZE(next);
        list_remove(next);
    }

    PUT(hp, PACK(size, PREV_ALLOCATED(hp)));
    PUT(FOOTER_P(hp), size);

    list_insert(hp);

    return hp;
}

// 懒惰合并，之后free时会进行coalesce，插入到对应的free list中
// size会保证至少是MIN_EXPAND_SIZE
// 扩展堆空间大小，返回扩展后的块的指针
// 需要注意的是，扩展后的块在这里发生合并，但是并没有插入到对应的free list中
static void *extend(size_t size) {

    size = MAX(size, MIN_EXPAND_SIZE);

    size_t *hp = mem_sbrk(size);
    if (hp == (void *)-1)
        return NULL;

    hp -= 1;
    PUT(hp, PACK(size, PREV_ALLOCATED(hp)));
    DEREF((char *)hp + size) = 1;

    //coalesce without insert
    void *prev = PREV_HEADER_P(hp);
    void *next = NEXT_HEADER_P(hp);
    int prev_alloc = PREV_ALLOCATED(hp);
    int next_alloc = ALLOCATED(next);

    if(!prev_alloc){
        size += BLOCK_SIZE(prev);
        list_remove(prev);
        hp = prev;
    }
    if(!next_alloc){
        size += BLOCK_SIZE(next);
        list_remove(next);
    }

    PUT(hp, PACK(size, PREV_ALLOCATED(hp)));
    PUT(FOOTER_P(hp), size);

    return hp;
}