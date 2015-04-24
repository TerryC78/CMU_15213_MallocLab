/*
 * mm.c
 *
 * name: Tianyu Chen
 * Andrew ID: tianyuc
 *
 * COMMENTS: this is a memory allocator using 10 segregated list and best
 *           fit. Allocated block footer removed. Address into 4 bytes.
 *
 * Segregated list:
 * #1 ten free lists: 1-2 DSIZE, 3 DSIZE, 4DSIZE, 5-8DSIZE, 9-16DSIZE
 *    17-32DSIZE, 33-64DSIZE, 65-128DSIZE, 129-256DSIZE, >256DSIZE
 * #2 every free block in segregated list has 
 *    1) a header: 
 *    which indicates size, whether this block is the tail of the free list
 *    the allocation condition of previous block, and the allocation 
 *    condition of itself. For example header with (size,1,1,0) means "
 *    -> This free block totally has size byte; 
 *    -> This is a tail node in free list; (the first 1)
 *    -> The previous block is allocated; (the second 1)
 *    -> This is a free block (the 0)
 *   
 *    2) a footer: 
 *    size and allocation condition of itself
 *    3) previous free block pointer(4 Byte):
 *    in macro ADDR2INT, I change address into an int to save space
 *    points to the previous free block, if no previous free block,
 *    points to the pointer which points it
 *    4) next free block pointer(4 Byte):
 *    points to the next free block, if no next free block set 0x0
 * #3 for allocated blocks, footer is removed
 * #4 in mm_init, I use the 15 WSIZE to store 10 pointers to the ten 
 *    heads of the segregated lists
 *
 * Best Fit:
 * #1 in find_fit, if we find the free block which is the same size as
 *    asize, then return bp; otherwise, the allocator will record the candidate
 *    and check the next free block. If even no candidates found, turn to next
 *    free list
 *
 * For macros:
 * #1 NEXT_IBLKP(bp) returns the address of next block beside current
 *    block whatever allocated or not
 * #2 NEXT_EBLKP(bp) returns the address of next free block in the same 
 *    segerated list
 * #3 PREV_IBLKP(bp) & PREV_IBLKP(bp), similar to NEXT_IBLKP & NEXT_EBLKP
 *    but points to the previous blocks
 * #4 ADDR2INT: address(64 bits) into int(32 bits)
 *    minus the heap_start (so I am NOT simply minus 0x800000000 here)
 *     
 * #5 INT2ADDR: int into address
 *    plus the heap_start 
 * #6 FREE_NEXT_HDRP(bp), ALLOC_NEXT_HDRP(bp):
 *    Because the previous block allocation condition is stored in the 
 *    header of the current block, this macros are used to set the header
 *    or get the header
 * #7 SET_TAIL(bp), GET_TAIL(bp):
 *    Set this block is a tail node and get the tail node tag, which is 
 *    mentioned in "header" part of this comment.
 *
 *    Finally, thanks for all the TAs. I met some garbled bytes problem at 
 *  first and you helped me by advising me to remove coalecse, so there 
 *  is a #define GARBLED macro. But I didn't remove the define stuff, 
 *  for future debugging.
 *    :D
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <assert.h>
//#include <math.h>
//#include <tgmath.h>

#include "mm.h"
#include "memlib.h"


/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
//#define DEBUG
//#define PRINT
//#define GARBLED
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* MACRO by myself */
/* Basic constants and macros */
#define EMPTY 0 /* indicate if the free list is empty */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNKSIZE (1<<9) /* Extend heap by this amount (bytes) */
#define MAX_HEAP (1<<12) /* 1<<32 bytes = 4GB */
#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_ALLOC_FT(p) (GET(p) & 0x2)
#define GET_TAIL(p) (GET(p) & 0x4)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define PREVIOUS(bp) (*((unsigned int *)(bp) + 1))
#define FORWARD(bp) (*(unsigned int *)(bp))
#define FREE_NEXT_HDRP(bp) (*HDRP(NEXT_IBLKP(bp)) &= ~0x2)
#define ALLOC_NEXT_HDRP(bp) (*HDRP(NEXT_IBLKP(bp)) |= 0x2)
#define SET_TAIL(bp) (*HDRP(bp) |= 0x4)

/* Given block ptr bp, compute address of next and previous blocks */
#define PREV_IBLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))
#define NEXT_IBLKP(bp) ((char *)(bp) + GET_SIZE(HDRP((char *)(bp))))
#define PREV_EBLKP(bp) (INT2ADDR(PREVIOUS(bp)))
#define NEXT_EBLKP(bp) (INT2ADDR(FORWARD(bp)))

/* mm-naive.c */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

/* save address space */
#define ADDR2INT(bp) ((unsigned int)(long)(bp - heap_start))
#define INT2ADDR(uint) ((char *)((long)uint + heap_start))

/* Private global variables */
#ifdef DEBUG
static int operation_num; /* Record operation times, for debugging */
#endif
static char *heap_listp; /* Points to the empty heap */
static char *heap_brk; /* Points to the last heap block */
static long heap_start; /* Record the start of the heap to make 64 bits 
 address into 32 bit unsigned int */

void *extend_heap(size_t words);
#ifndef GARBLED
void *coalesce(void *bp);
#endif
void *find_fit(size_t asize);
void place(void *bp, size_t asize);
void delete_node(void *bp);
void add_node(void *bp);
void *search_list(void *search_start, size_t asize);
void *find_list(size_t asize);

#ifdef DEBUG
//#ifdef PRITN
//static void printblock(void *bp);
//#endif
static void checkblock(void *bp);
static void checkfreelist(int verbose);
#endif

/*
 *initialize: return -1 on error, 0 on success.
 * initialize the heap and the segregated poionters
 */
int mm_init(void) {
    int i;
#ifdef DEBUG
    operation_num = 0;
#endif
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(14*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0); /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(6*DSIZE, 1));/* Prologue header */
    PUT(heap_listp + (12*WSIZE), PACK(6*DSIZE, 1));/* Prologue footer */
    PUT(heap_listp + (13*WSIZE), PACK(0, 3)); /* Epilogue header */
    heap_start = (long)heap_listp;
    heap_listp += (2*WSIZE);
    heap_brk = heap_listp + (12*WSIZE);

    for (i = 0; i < 10; i++){
        /* initialize the segregated list points to heap_brk */
        PUT(heap_listp + (i*WSIZE), EMPTY);  
    }
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * malloc
 * the malloc funtion, allocate the block
 * first find best-fit free block and then place it
 *
 */
void *malloc (size_t size) {
    size_t asize; /* Adjusted block size */
    size_t extendsize;/* Amount to extend heap if no fit */
    
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else    
        asize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
#ifdef DEBUG
        mm_checkheap(1);
        checkfreelist(1);
#endif
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
        place(bp, asize);
#ifdef DEBUG
        mm_checkheap(1);
        checkfreelist(1);
#endif
        return bp;
}

/*
 * free
 * free funtion, free those allocated blocks
 * first change the header and footer then coalecse
 */
void free (void *bp) {
    if (bp == 0)
        return;

    size_t size = GET_SIZE(HDRP(bp));

    if (heap_listp == 0){
        mm_init();
    }
     
    PUT(HDRP(bp), PACK(size, GET_ALLOC_FT(HDRP(bp))));
    PUT(FTRP(bp), PACK(size, 0));
#ifndef GARBLED
    coalesce(bp);
#endif
#ifdef DEBUG
    mm_checkheap(1);
    checkfreelist(1);
#endif
}

/*
 * realloc - you may want to look at mm-naive.c
 * this is the same as the original version
 */
void *realloc(void *oldptr, size_t size) {
    size_t oldsize;
    void *newptr;
       
    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
       free(oldptr);
       return 0;
    }
                              
    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
       return malloc(size);
    }
                                               
    newptr = malloc(size);
                                                   
    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
       return 0;
    }
                                                                     
    /* Copy the old data. */
    oldsize = *SIZE_PTR(oldptr);
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);
                               
    /* Free the old block. */
    free(oldptr);
                                               
    return newptr; 
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

#ifdef DEBUG
/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;}
#else
#endif

/*
 * extend_heap - extend the heap size
 * if the heap is not enough to store the allocated blocks then call
 * this function
 *
 */
void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    int ft_allocate = GET_ALLOC_FT(HDRP(heap_brk));
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, ft_allocate));

    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */

    heap_brk = NEXT_IBLKP(bp);  /* record new heap_brk */
    PUT(HDRP(heap_brk), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
#ifndef GARBLED
    return (coalesce(bp));
#else
    return bp;
#endif
}

/*
 * coalesce - make free blocks right
 * there are four cases, depending on the allocation condition of the
 * previous block and the next block
 *
 */
#ifndef GARBLED
void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC_FT(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_IBLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) { /* Case 1 */

        /* then set values */
        PUT(HDRP(bp), PACK(size, 2)); /* remove footer */
        PUT(FTRP(bp), PACK(size, 0));
        FREE_NEXT_HDRP(bp);

        add_node(bp);
               
        return bp;
    }

    else if (prev_alloc && !next_alloc) { /* Case 2 */
    
        delete_node(NEXT_IBLKP(bp));

        /* same as case 3 and then move the list to current block */
        size += GET_SIZE(HDRP(NEXT_IBLKP(bp)));
        PUT(HDRP(bp), PACK(size, 2));
        PUT(FTRP(bp), PACK(size, 0)); 
        
        add_node(bp);

        return bp;
    }

    else if (!prev_alloc && next_alloc) { /* Case 3 */
        delete_node(PREV_IBLKP(bp));
        /* increase the previous free block size */
        size += GET_SIZE(HDRP(PREV_IBLKP(bp)));
        /* remove the allocated tag */
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_IBLKP(bp)), PACK(size, 0x2));
        FREE_NEXT_HDRP(bp);
        bp = PREV_IBLKP(bp);

        add_node(bp);
        return bp;
    }

    else { /* Case 4 */
        /* change previous size and free next size */
        delete_node(PREV_IBLKP(bp));
        delete_node(NEXT_IBLKP(bp));
        size += GET_SIZE(HDRP(PREV_IBLKP(bp))) +
        GET_SIZE(HDRP(NEXT_IBLKP(bp)));
        PUT(HDRP(PREV_IBLKP(bp)), PACK(size, 2));
        PUT(FTRP(PREV_IBLKP(bp)), PACK(size, 0));
        bp = PREV_IBLKP(bp);

        add_node(bp);
        return bp;
    }
}
#endif

/*
 * find_fit - to find the best free block
 * best fit strategy, details are in search_list function
 *
 */
void *find_fit(size_t asize){
    /* best fit */
    void *bp, *search_fit;
    bp = find_list(asize);
    search_fit = search_list(bp, asize);
    
    while (search_fit == NULL){
        bp += WSIZE;
        if (bp == heap_listp + 10*WSIZE){
            return NULL;
        }
        search_fit = search_list(bp, asize);
    }
    return search_fit;
}

/*
 * search_list - return the right free block according to asize
 * best fit strategy. if this function find the same free block as the 
 * asize one, return the pointer to that free block, otherwise save it as
 * a candidate. If no 
 *
 */
void *search_list(void *search_start, size_t asize){
    /* first fit */
/*    void *bp;
    if (FORWARD(search_start) == 0){
        return NULL;
    }
    for (bp = NEXT_EBLKP(search_start); ADDR2INT(bp) != EMPTY;
        bp = NEXT_EBLKP(bp)) {
        if (~GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize){
            return bp;
        }
    }
*/
    /* best fit */
    void *bp, *candidate;
    size_t candidate_size, current_size;
    candidate_size = 0xffffffff; /* large enough */
    candidate = NULL;
    if (FORWARD(search_start) == EMPTY){
        return NULL;    
    }
    
    for (bp = NEXT_EBLKP(search_start); ADDR2INT(bp) != EMPTY;
         bp = NEXT_EBLKP(bp)) {
        current_size = GET_SIZE(HDRP(bp));
        if (current_size == asize){
            return bp;
        }
        else if((current_size > asize) && (current_size < candidate_size)){  
            candidate_size = current_size;
            candidate = bp;
        }
        else{
        }
    }
    if (candidate != NULL){
    /* no fit found in current */
        return candidate;
    }
    else{
        return NULL;
    }
    
}

/*
 * delete_node - delete current free block from free list
 * there are different cases which are listed in the comments below
 * also change the forward and previous pointers
 *
 */
void delete_node(void *bp){
    if (GET_TAIL(HDRP(bp))){ /* if it's tail node */
        /* check if there is another node in current free list */
        if (PREVIOUS(bp) < 0x34){ /* no other nodes found */
            PUT(PREV_EBLKP(bp), EMPTY);  /* this list is empty */
        }
        else { /* if there is another node left */
        //set tail node
            PUT(PREV_EBLKP(bp), EMPTY);
            SET_TAIL(PREV_EBLKP(bp));
        }
        return;
    }
    /* if it's not tail node */
    
    PUT(PREV_EBLKP(bp), FORWARD(bp));
    PUT(NEXT_EBLKP(bp) + WSIZE, PREVIOUS(bp));
}

/*
 * add_node - add current free block into the free list
 * First check whether this is the tail node then change the forward 
 * and previous pointers
 *
 */

void add_node(void *bp){
    void *list_ptr;
    /* check which list it should be in */
    list_ptr = find_list(GET_SIZE(HDRP(bp)));
    /* then add node to that list */
    if (FORWARD(list_ptr) == EMPTY){     /* tail node */
        PUT(list_ptr, ADDR2INT(bp)); /* heap node points to new node */
        PUT(bp, EMPTY);  /* insert new node */
        PUT(bp + WSIZE, ADDR2INT(list_ptr));
        SET_TAIL(bp); /* this is the new tail node */
        return; 
    }

    PUT(bp + WSIZE, ADDR2INT(list_ptr));  /* set new node */

    PUT(bp, ADDR2INT((void *)NEXT_EBLKP(list_ptr)));

    PUT(NEXT_EBLKP(bp) + WSIZE, ADDR2INT(bp));/* then set nodes near 
    new node*/
    PUT(list_ptr, ADDR2INT(bp));
}

/*
 * find_list - return the right free list according to asize
 * Just by checking the asize one by one, maybe I should use BST to 
 * improve the speed but I didn't try that.
 *
 */
void *find_list(size_t asize){
   
    if (asize <= 2*DSIZE){
        return heap_listp;    
    }
    else if (asize <= 3*DSIZE){
        return heap_listp + WSIZE;
    }
    else if (asize <= 4*DSIZE){
        return heap_listp + 2*WSIZE;
    }
    else if (asize <= 8*DSIZE){
        return heap_listp + 3*WSIZE;
    }
    else if (asize <= 16*DSIZE){
        return heap_listp + 4*WSIZE;
    }
    else if (asize <= 32*DSIZE){
        return heap_listp + 5*WSIZE;
    }
    else if (asize <= 64*DSIZE){
        return heap_listp + 6*WSIZE;
    }
    else if (asize <= 128*DSIZE){
        return heap_listp + 7*WSIZE;
    }
    else if (asize <= 256*DSIZE){
        return heap_listp + 8*WSIZE;
    }
    else {
        return heap_listp + 9*WSIZE;
    }
}

/*
 * place - place the allocated block
 * two cases are discussed here
 *
 */
void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= (2*DSIZE)) {
        delete_node(bp);
        /* first put in the size and allocation information */
        PUT(HDRP(bp), PACK(asize, 3));
       
        /* add new node */ 
        bp = NEXT_IBLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 2));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        add_node(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 3));
        ALLOC_NEXT_HDRP(bp);
        delete_node(bp);
    }
    return;
}


/*
 * mm_checkheap
 *  At first I just print the whole heap to debug which seems good for me
 * And then I realize I cannot print the heap everytime so I just make 
 * the print stuff into commensts.
 *  The mm_checkheap function will check 
 *  1) whether the size is right, 
 *  2) whether the prologue is right or not
 *  3) whether the epilogue is right or not
 *  4)  all other blocks are right or not by checkblock function
 *
 */
#ifndef DEBUG
void mm_checkheap(int lineno){
    lineno = lineno;
    return;    
}
#else
void mm_checkheap(int verbose) {
    char *bp = heap_listp;
    operation_num++;
/*    if (verbose){
        dbg_printf("---------------check heap starts----------------\n");
        dbg_printf("This is the %dth operation\n", operation_num);
        dbg_printf("Heap (heap_listp = %p):\n", heap_listp);
         // Heap information 
    } */

    /* check prologue header */
    if (GET_SIZE(HDRP(heap_listp)) != 6 * DSIZE){
        dbg_printf("Bad prologue header: size error\n");
        exit(1);    
    } 
    if (!GET_ALLOC(HDRP(heap_listp))){
        dbg_printf("Bad prologue header: allocate error\n");
        exit(1);
    }

    /* check prologue footer */
    if ((GET_SIZE(FTRP(heap_listp)) != 6 * DSIZE)){
        dbg_printf("Bad prologue footer: size error\n");
        exit(1);
    }
    if (!GET_ALLOC(FTRP(heap_listp))){
        dbg_printf("Bad prologue footer: allocate error\n");
        exit(1);
    } 

    /* check each block's alignment ,header & footer */
    for (bp = heap_listp + 12*WSIZE; GET_SIZE(HDRP(bp)) > 0;
         bp = NEXT_IBLKP(bp))
    {
        if (verbose){
/* #ifdef PRINT
                printblock(bp); 
#endif */
                checkblock(bp);
        }
    }

    /* print the epilogue 
    if (verbose){
        printblock(bp);
    }  */
    
    /* check epilogue block */
    if (GET_SIZE(HDRP(bp)) != 0) {
        dbg_printf("Bad epilogue header: size error\n");
        exit(1);
    }
        
    if (!GET_ALLOC(HDRP(bp))){
        dbg_printf("Bad epilogue header: allocate error\n");
        exit(1);
    }
    return;
}

/*
 * printblock - print the current state of the free block
 * if this is a free block, it will also print the previous pointer and
 * next pointer
 *
 */
/*#ifdef PRINT
static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
        dbg_printf("EOL (heap_brk = %p)\n", heap_brk);
        dbg_printf("----------------check heap ends----------------\n");
        return;
    }
    if (GET_ALLOC(HDRP(bp))){
        dbg_printf("  %p: header[%p:%c]=#=footer[%p:%c]\n", bp, 
             (void *)hsize, (halloc ? 'a' : 'f'), (void *)fsize,
            (falloc ? 'a' : 'f'));
    }
    else {
        dbg_printf("  %p: header[%p:%c]   footer[%p:%c]\n", bp, 
             (void *)hsize, (halloc ? 'a' : 'f'), (void *)fsize,
            (falloc ? 'a' : 'f')); 
        dbg_printf("    FORWARD -> %p  PREVIOUS <- %p\n", 
            INT2ADDR(FORWARD(bp)), INT2ADDR(PREVIOUS(bp)));
    }
}
#endif*/


/*
 * checkblock - check the correctness of the free block
 * this function will check for the size, whether it is aligned or not
 * and if there are two consecutive free blocks in the heap, if the 
 * header matches the footer 
 *
 */
static void checkblock(void *bp) 
{
    /* check if the block is too small */
    if ((GET_SIZE(HDRP(bp)) < DSIZE) && (GET_SIZE(HDRP(bp)) > 0)){
        dbg_printf("Error: block %p is too small\n", bp);    
        exit(0);
    }

    /* check if the block is doubleword aligned */
    if (!aligned(bp)){
        dbg_printf("Error: %p is not doubleword aligned\n", bp);
        exit(0);
    }
   
    /* check if the free block header matches the block footer */
    
    if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) != GET_SIZE(FTRP(bp))){
        dbg_printf("Error: header does not match footer\n");
        exit(0);
    } 

    /* check if there are two consecutive free blocks in the heap */
    if (!GET_ALLOC(HDRP(NEXT_IBLKP(bp))) && !GET_ALLOC(HDRP(bp))) {
        dbg_printf("Error: two consecutive free blocks: %p and %p\n",
         bp, NEXT_IBLKP(bp));
        exit(0);
    }
}

/*
 * checkfreelist - to check all segregated free lists
 * this function will check the free list from the head node to tail node
 * 1) whether the next pointer and previous pointer is right
 * 2) whether they link with each other
 * 3) whether the pointer points inside the heap
 * 4) whether the allocated tag is right
 *
 */

static void checkfreelist(int verbose)
{
    char *bp;
    int  j;
    verbose = verbose;
    /* for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_IBLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp))) 
            break;  obtain the first free block 
    }  
    */
/*#ifdef PRINT    
   if (verbose){
        dbg_printf("----------------check free list-----------------\n")
        ;
        for (j = 0; j < 10; j++){
            i = 0;
            dbg_printf("Check free list forward:\n");
            dbg_printf("  Free list[%d] starts at %p\n",
                    j, INT2ADDR(heap_listp[j]));
            if (NEXT_EBLKP(heap_listp + j*WSIZE) != INT2ADDR(0)){
                for (bp = heap_listp + j*WSIZE; FORWARD(bp) != EMPTY;
                    bp = NEXT_EBLKP(bp)){
                    i++;
                    dbg_printf("    Free-list[%d](%d): %p\n", j, i, bp);
                }
        dbg_printf("Free list last: %p\n", bp);
                dbg_printf("  Free list[%d] ends at %p\n", j, bp);
                dbg_printf("Check free list backward:\n");
                dbg_printf("  Free list ends at %p\n", bp);
                for (bp = bp; PREVIOUS(bp) > 0x3c;
                    bp = PREV_EBLKP(bp)){
                    dbg_printf("    Free-list[%d](%d): %p\n", j, i, bp);
                    i--;
                }
                bp = PREV_EBLKP(bp);
                dbg_printf("  Free list[%d] starts at %p\n", j, bp);
            }
            else{
                dbg_printf("  Free list[%d] ends at %p\n", j, heap_brk);
            }
        }
        dbg_printf("----------------check free list-----------------\n")
        ;
    }
#endif */

    /* check whether consecutive free blocks are consistent */
    for (j = 0; j < 10; j++){
        for (bp = heap_listp + j*WSIZE; (FORWARD(bp) != EMPTY) && 
            (!GET_TAIL(HDRP(bp)));
            bp = NEXT_EBLKP(bp)){
            if (FORWARD(bp) != EMPTY){
            if (!in_heap(bp)){
                dbg_printf("Error: freelist pointer %p out of reap\n", 
                bp);   
                exit(0);
            }
            if (INT2ADDR(FORWARD(bp)) != NEXT_EBLKP(bp) || 
                PREVIOUS(NEXT_EBLKP(bp)) != ADDR2INT(bp)){
                dbg_printf("Error: freelist %p doesn't match next block\n"
                , bp);
                exit(0);
            }   

            /* check each forward pointer whether correct or not*/
            if ((GET_ALLOC(HDRP(NEXT_EBLKP(bp))) == 1) &&
                NEXT_EBLKP(bp) != heap_brk){
                dbg_printf(
                "Error: freelist %p forward points to wrong block\n", bp);
                exit(0);
            }

            /* check each previous pointer whether correct or not */
            if (ADDR2INT(bp) > 0x34 && (GET_ALLOC(HDRP(PREV_EBLKP(bp))) ==
                 1) 
                && PREV_EBLKP(bp) != heap_listp+j*WSIZE){
               dbg_printf(
               "Error: freelist %p previous points to wrong block\n"
                , bp);
                exit(0);
            }
            }

        /* if (explicit_first != NULL && GET_ALLOC(HDRP(explicit_first)))
            {
                dbg_printf("Error: explicit_first is wrong 
                at %p\n", explicit_first);    
                exit(0);
            }       

            if (explicit_last != NULL && GET_ALLOC(HDRP(explicit_last))){
                dbg_printf("Error: explicit_last is wrong at %p\n",
                 explicit_last);    
                 exit(0);
            }
            */ 
    /* count free blocks by iterating through every block and
     *  traversing free list by pointers and see if they match */
        }
    }
}
#endif


