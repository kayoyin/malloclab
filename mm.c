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

/* Macros for explicit free list */
/* Read and write a word to successor free block of current free block*/
#define GET_PREV(bp) (*(unsigned int *)(bp))
#define PUT_PREV(p, val) (*(unsigned int *)(bp) = (val))
#define GET_SUCC(bp) (*(unsigned int *)(bp+1))
#define PUT_SUCC(p, val) (*(unsigned int *)(bp+1) = (val))
/* Dereference void pointer*/
//#define PTR_VAL(bp) (*(int*)bp)

/* Macros for mm_check */
#define GET_FLAG(bp) (*(unsigned int *)(bp+2))
#define PUT_FLAG(bp, val) (*(unsigned int *)(bp+2) = (val))


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
    PUT(heap_listp + (3 * WSIZE), 0); /* predeccessor pointer */
    PUT(heap_listp + (4 * WSIZE), 0); /* successor pointer */
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (3*WSIZE); // point to first block after prologue

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
  mm_check();
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
    place(bp, asize);
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
  int prev,succ;

  if (prev_alloc && next_alloc) {
      prev = heap_listp; // first block
      for (succ = GET_SUCC(heap_listp); succ>0; succ = GET_SUCC(succ)){
        if (succ > bp) // succ block located after bp physically
        { // put bp between prev and succ
          PUT_PREV(succ, bp);
          PUT_SUCC(bp, succ);
          PUT_PREV(bp,prev);
          PUT_SUCC(prev,bp);
          return bp;
        }
        prev = succ; // succ before bp so predecessor of bp
      }
      PUT_SUCC(bp, succ);
      PUT_PREV(bp, prev);
      PUT_SUCC(prev,bp);
      return bp;
  }

  else if (prev_alloc && !next_alloc) {
      size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
      prev = GET(NEXT_BLKP(bp));
      succ = GET_SUCC(NEXT_BLKP(bp));
      PUT(HDRP(bp), PACK(size,0));
      PUT(FTRP(bp), PACK(size,0));
      PUT_PREV(bp, prev);
      PUT_SUCC(bp, succ);
      if (succ > 0){
        PUT_PREV(succ, bp);
      }
      PUT_SUCC(prev, bp);
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
      succ = GET_SUCC(NEXT_BLKP(bp));
      bp = PREV_BLKP(bp);
      PUT_SUCC(bp, succ);
      if (succ > 0){
        PUT_PREV(succ, bp);
      }

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
  unsigned int bp;

  for (bp = (int)heap_listp; bp != 0; bp = GET_SUCC(bp)) {
    if ((GET_SIZE(HDRP(bp)) >= asize)) {
      return (void *)bp;
    }
  }
  return NULL; /* No fit */

}

// Allocate block of size asize starting at bp, split if necessary (there's remainder)
static void place(void *bp, size_t asize)
{
  size_t size = GET_SIZE(HDRP(bp)); // size of free block
  int prev = GET_PREV(bp);
  int succ = GET_SUCC(bp);

  if ((size - asize) >= (2*DSIZE)) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(size-asize, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size-asize, 0));
    if (succ != 0){
      PUT_PREV(succ, bp);
    }
    PUT_SUCC(prev, bp);
    PUT_PREV(bp,prev);
    PUT_SUCC(bp,succ);
  }
  else { // no split
    PUT(HDRP(bp), PACK(size, 1));
    PUT(FTRP(bp), PACK(size, 1));
    if (succ != 0){
      PUT_PREV(succ, prev);
    }
    PUT_SUCC(prev,succ);

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

void exit_with_error(char *message)
{
	fprintf(stderr, "%s\n", message);
	printf("INVALID \n");
	exit(EXIT_FAILURE);
}

void mmcheck(void)
{
  void *heapfirst;
  void *heaplast;
  void *header;
  void *footer;
  void *bp;

  heapfirst = mem_heap_lo();
  heaplast = mem_heap_hi();

  if (heaplast >= mem_heapsize() + heapfirst) exit_with_error("last byte goes beyond heap space");


  for (bp = NEXT_BLKP((int)heap_listp); bp != 0; bp = NEXT_BLKP(bp)) {
    if ((bp < heapfirst) || (bp > heaplast)) exit_with_error("access outside heap space");
    if (GET_ALLOC(bp) == 0){
      PUT_FLAG(bp,0xDEADBEEF);
      if (PREV_BLKP(bp) == 0){
        exit_with_error("free block escaped coalescing");
      }
    }
    header = HDRP(bp);
    footer = FTRP(bp);
    if (GET(header) != GET(footer)) exit_with_error("header and footer don't match");
  }

  for (bp = (int)heap_listp; bp != 0; bp = GET_SUCC(bp)) {
    if (GET_ALLOC(bp) == 1) exit_with_error("a block in the free list is not actually free");
    if (GET_FLAG(bp) != 0xDEADBEEF) exit_with_error("a free block is not in the free list");
    if (GET_PREV(GET_SUCC(bp)) != GET_SUCC(GET_PREV(bp))) exit_with_error("the successor of the predecessor is not the predecessor of the successor");
  }

}
