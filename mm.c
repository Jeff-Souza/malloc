/*
 * At first, we started implementing an explicit implementation of the lab
 * and faced many problems concerning pointer manipulation and 
 * internal fragmentation bugs.
 * We had to fall back on implementing an implicit free list because of time constraints
 * and ended up with a full understanding of malloc
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your identifying information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "JeffAndRaj",
    /* First member's full name */
    "Jeffrey Souza",
    /* First member's UID */
    "u0402450",
    /* Second member's full name (leave blank if none) */
    "Rajul Ramchandani",
    /* Second member's UID (leave blank if none) */
    "u0912654"
};

// word size: 4 bytes
#define WSIZE 4
// double word alignment: 8 bytes
#define DSIZE 8
// maximum memory: 2^12 bytes
#define CHUNKSIZE (1<<12)

// HEADER + FOOTER size = 8 bytes
#define OVERHEAD 8

// Macros for accessing and altering blocks
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))       // Set footer/header
/* Read and write a word at address p */
#define PUT(p, val)        (*(size_t *)(p) = (val)) // Put val in word at address p
#define GET(p)             (*(size_t *)(p))         // Get word from address p
/* Read the size and allocated fields from address p */
#define GET_SIZE(p)        (GET(p) & ~0x7)          // Get size of block whose header is at address p (make the last 3 bits)
#define GET_ALLOC(p)       (GET(p) & 0x1)           // Get allocation status of block

// Macros for traversing blocks
/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)           ((char *)(bp) - WSIZE)                            // Get header pointer from block pointer
#define FTRP(bp)           ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)       // Get footer pointer from block pointer
/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)      ((char *)(bp) + GET_SIZE(((char *)(bp) -WSIZE)))  // Get pointer to next block of p
#define PREV_BLKP(bp)      ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // Get pointer to previous block of p

#define MAX(a, b) ((a > b) ? a : b)


// Macros for explicit free list

// Pointer to the previous free block of bp in the free list
#define GET_PREV_FREE_BLKP(bp) (*(void **) (bp))
// Pointer to the next free block of bp in the free list
#define GET_NEXT_FREE_BLKP(bp) (*(void **) (bp + WSIZE))
// Set the previous free block of the block pointed by bp in free list
#define SET_PREV_FREE_BLKP(bp, prev) (*((void **)(bp)) = prev)
// Set the next free block of the block pointed by bp in free list
#define SET_NEXT_FREE_BLKP(bp, next) (*((void **)(bp + WSIZE)) = next)

// forward declarations

static void *extend_heap(size_t words);
static void *coalesce(void *bp);

static void *findOpenSpot(size_t asize);
static void addBlock(void *bp);
static void placeBlock(void *bp, size_t asize);
static void removeBlock(void *bp);

// single word (4), double word (8) alignment
#define ALIGNMENT 8

// rounds to nearest multiple of ALIGNMENT
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// Points to the starting address of the heap
void *heap_start_ptr;
// Points to the head of the explicit free list, null when the heap has not been created
void *head_FreeList = NULL;

/* 
 * mm_init - initialize the malloc package.
 *
 */
int mm_init(void) {
    /* Create the initial empty heap */
    if ((heap_start_ptr = mem_sbrk(4 * WSIZE)) == (void *) -1) // returns the pointer to start of heap
        return -1;
    
    PUT(heap_start_ptr, 0); /* Alignment padding */
    PUT(heap_start_ptr + WSIZE, PACK(OVERHEAD, 1)); /* Prologue header */
    PUT(heap_start_ptr + DSIZE, PACK(OVERHEAD, 1)); /* Prologue footer */
    PUT(heap_start_ptr + WSIZE + DSIZE, PACK(0, 1)); /* Epilogue header */

    heap_start_ptr += DSIZE;
    head_FreeList=NULL; // Initial Free list Pointer NULL

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == (void *) -1)
        return -1;

    return 0;
}

/*
 * extend_heap - Extends the heap when the desired memory is not available
 * pg 831
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size = words * WSIZE;

    /* Allocate an even number of words to maintain alignment */
    size = ALIGN(size + SIZE_T_SIZE);
    if ((int)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* Free block epilogue */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * coalesce - Merges two free blocks
 * pg 833
 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        addBlock(bp); // add the free block to free list
        return bp;
    } else if (prev_alloc && !next_alloc) {
        removeBlock(NEXT_BLKP(bp)); // remove next free block
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));        
        addBlock(bp); // add new merged free block into list
    } else if (!prev_alloc && next_alloc) {
        removeBlock(PREV_BLKP(bp)); // remove prev free block
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        addBlock(bp); // add the new merged free block into list
    } else {
	// if next and previous blocks are free remove both
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));

        size+=GET_SIZE(HDRP(PREV_BLKP(bp)));
        size+=GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        addBlock(bp); // add the new merged block in the list
    }
    return bp; // Pointer to the newly merged free block
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 *   pg 834
 */
void *mm_malloc(size_t size){
        size_t asize; /* Adjusted block size */
        size_t extendsize; /* Amount to extend heap if no fit */
        char *bp;

        /* Ignore spurious requests */
        if (size == 0) 
        	return NULL;

        /* Adjust block size to include overhead and alignment reqs. */
        if (size <= DSIZE) {
             asize = DSIZE+OVERHEAD; // 8 + 8 = 16 byte block, min payload: 8 bytes
	} else {
             asize = ALIGN(size+SIZE_T_SIZE);
	} 

	/* Search the free list for a fit */
	if ((bp = findOpenSpot(asize)) != NULL) { // find first fit block in the heap
            placeBlock(bp, asize); // placeBlock headers and footers in block
            return bp;
        }

        /* No fit found. Get more memory and placeBlock the block */
        extendsize = MAX(asize,CHUNKSIZE);
        if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
            return NULL;
        placeBlock(bp, asize);

        return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if(ptr == NULL && size != 0) { // If the ptr is NULL and size is nonzero then just do malloc
        void* payload = mm_malloc(size);
        return payload;
    }

    if(size == 0) {
        if(ptr == NULL) {
	    return NULL; // Not applicable
	}
        mm_free(ptr);
        return ptr;
    }

    // Realloc Implementation
    void *old_bp = ptr;
    void *new_bp;
    size_t old_size;
    
    new_bp = mm_malloc(size); // New block of new size
    if (new_bp == NULL) { // If no enough memory available
        return NULL;
    }
    old_size = *(size_t *)((char *)old_bp - WSIZE); // Old block Size

    if (size < old_size) {
        old_size = size;
    }

    memcpy(new_bp, old_bp, old_size);
    mm_free(old_bp); // Frees the old ptr (Block)

    return new_bp;
}	

/*
 * mm_free
 * pg 833
 */
void mm_free(void *ptr)
{
    if(heap_start_ptr == 0) {
	mm_init(); // If the heap is not intialised and free occurs
    }

    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr); // Merge the block to the previous and/or next free block
}

/*
 * findOpenSpot - Implements the routine to find the first fit block
 *
 */
static void *findOpenSpot(size_t asize) {
    void *bp;

    //  Search the free list untill we find a free block
    for (bp = head_FreeList; bp!=NULL ; bp = GET_NEXT_FREE_BLKP(bp)){
        if (asize <= GET_SIZE(HDRP(bp))) {
    	    return bp;
        }
    }
    return NULL; // Return NULL if no block of memory big enough can be found
}

/*
 * addBlock - adds the block in the freelist according to its address
 *
 */
static void addBlock(void *bp) {
    void *current = head_FreeList;
    void *temp = current;
    void *prev = NULL;

    while (current != NULL && bp < current) {
        prev = GET_PREV_FREE_BLKP(current);      // prev free block 
        temp = current;                          // save current free block pointer
        current = GET_NEXT_FREE_BLKP(current);   // get next free block pointer
    }

    // Inserts bp in the Explicit Free list
    SET_PREV_FREE_BLKP(bp, prev);
    SET_NEXT_FREE_BLKP(bp, temp);

    if (prev != NULL) {
        SET_NEXT_FREE_BLKP(prev, bp);
    } else { // Insert bp before current free list head
        head_FreeList = bp;
    } if (temp != NULL) {
        SET_PREV_FREE_BLKP(temp, bp);
    }
}

/*
 * placeBlock - placeBlocks the Headers and footers in the block , also performs spilliting if neccessary
 *
 */
static void placeBlock(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    // break the block if created block is bigger than 16 bytes
    if ((csize - asize) >= (DSIZE + OVERHEAD)) {
        removeBlock(bp);

        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        
        addBlock(bp);
    }
    // Do not split, just allocate the block's header and footer
    else { // Causes internal fragmentation
         PUT(HDRP(bp), PACK(csize, 1));
         PUT(FTRP(bp), PACK(csize, 1));

         removeBlock(bp);
    }
}

/*
 * removeBlock - removes the block in the freelist (Adjustment of Pointers)
 *
 */
static void removeBlock(void *bp) {
    void *next = (void *) GET_NEXT_FREE_BLKP(bp); // next free block 
    void *prev = (void *) GET_PREV_FREE_BLKP(bp); // prev free block 

    if (prev == NULL) {
        head_FreeList = next;
    } else {
        SET_NEXT_FREE_BLKP(prev, next);
    }

    if (next != NULL) {
        SET_PREV_FREE_BLKP(next, prev);
    }
}
