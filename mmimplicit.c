/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
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
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "P.E.S.P. (Pandas Eat Sweet Potato)",
    /* First member's full name */
    "Kayo Yin",
    /* First member's email address */
    "kayo.yin@polytechnique.edu",
    /* Second member's full name (leave blank if none) */
    "Shrey Aryan",
    /* Second member's email address (leave blank if none) */
    "shrey.aryan@polytechnique.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros
(obtained from the textbook) */

#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))
/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static void *find_fit(size_t asize);
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);

void *heap_listp;

/*
 * mm_init - create heap with a free block
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
      return -1;

    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
      return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
  size_t asize;
  size_t extendsize;
  void *bp;

  if (size == 0)
    return NULL;

  if (size <= DSIZE){
    asize = 2*DSIZE; // min block size: alignemnt + overhead of header, footer
  }
  else{ // overhead bytes, round up to nearest multiple of 8
    asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
  }

  /* Search the free list for a fit */
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize); // (optionally split excess?)
    return bp;
  }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize,CHUNKSIZE);
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL; // no more memory
  place(bp, asize);
  return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
 void mm_free(void *bp)
 {
   size_t size = GET_SIZE(HDRP(bp));

   PUT(HDRP(bp), PACK(size, 0));
   PUT(FTRP(bp), PACK(size, 0));
   coalesce(bp);
 }


static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc) {
      return bp;
  }

  else if (prev_alloc && !next_alloc) {
      size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
      PUT(HDRP(bp), PACK(size,0));
      PUT(FTRP(bp), PACK(size,0));
  }

  else if (!prev_alloc && next_alloc) {
      size += GET_SIZE(HDRP(PREV_BLKP(bp)));
      PUT(FTRP(bp), PACK(size, 0));
      PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
      bp = PREV_BLKP(bp);
  }
  else {
      size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
      PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
      PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
      bp = PREV_BLKP(bp);

  }
  return bp;
}

/*
 * Extend heap with new free block
 * (at initialization and when mm_malloc can't find fit)
 */
static void *extend_heap(size_t words)
{
  size_t size;
  void *bp;
  /* Allocate an even number of words to maintain alignment */
  // size = ALIGN(words);
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // round up to nearest 2 words
  if ((long)(bp = mem_sbrk(size)) == -1) return NULL;
  // receive memory after header o epilogue block -> header of new free block

  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
  PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue block header */
//  PUT(FTRP(PREV_BLKP(bp)), PACK(0, 1));
  /* Coalesce if the previous block was free */

  return coalesce(bp); // return block pointer to merged blocks
}

static void *find_fit(size_t asize)
{
  void *bp;

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if ((GET_ALLOC(HDRP(bp)) == 0) && (GET_SIZE(HDRP(bp)) >= asize)) {
      return bp;
    }
  }
  return NULL; /* No fit */

}

// Allocate block of size asize starting at bp, split if necessary (there's remainder)
static void place(void *bp, size_t asize)
{
  size_t size = GET_SIZE(HDRP(bp)); // size of free block

  if ((size - asize) >= (2*DSIZE)) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(size-asize, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size-asize, 0));
  }
  else { // no split
    PUT(HDRP(bp), PACK(size, 1));
    PUT(FTRP(bp), PACK(size, 1));
  }
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    size_t copySize;

    if (size == 0){
      mm_free(ptr);
      return 0;
    }

    if (ptr == NULL){
      return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    if (!newptr)
      return 0;

    copySize = MIN(GET_SIZE(HDRP(ptr)), size);
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}
