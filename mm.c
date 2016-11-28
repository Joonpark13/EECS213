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
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Cut the Crap",
    /* First member's full name */
    "Adrick Tench",
    /* First member's email address */
    "adricktench2018@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Joon Park",
    /* Second member's email address (leave blank if none) */
    "joonpark@u.northwestern.edu"
};

/* single word (4) or double word (8) */
#define ALIGNMENT 8
#define WSIZE 8 //word size, headers and footers
#define DSIZE 16 //double word size
#define LISTS 20 //number of free lists
#define CHUNKSIZE (1<<12)
#define MINBLOCK 32 //minimum block size (two 8 byte pointers + 8 byte headers and footers)

/* Following macros obtained from textbook, page 857 */

/* Min and Max of two values */
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) > (y) ? (x) : (y))

/* pack a size and allocated bit into word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define READ(p) (*(uint64_t *)(p))
#define WRITE(p, val) (*(uint64_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (READ(p) & ~0x7)
#define GET_ALLOC(p) (READ(p) & 0x1)

/* Given block ptr bp, compute address of its header */
#define HEADER(bp) ((char *)(bp) - WSIZE)
#define FOOTER(bp) ((char *)(bp) + GET_SIZE(HEADER(bp)) - DSIZE)

/* Given block ptr bp, compute address of (physically) next and previous blocks */
#define NEXT(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREVIOUS(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

/* end macros from textbook*/

/* Given block ptr bp, compute address of predecessor and successor */
#define PREDECESSOR(bp) (char *)(bp)
#define SUCCESSOR(bp) ((char *)(bp) + 8) //pointer is size 8

// Store predecessor or successor pointer for free blocks; works like write but ensures casting 
#define SET_PTR(p, val) (*(uint64_t *)(p) = (uint64_t)(val))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


//#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Global variables */
void *segregated_free_list[LISTS];
char *heap_start;

/* Helper function headers */
static void *extend_heap(size_t size);
static void *coalesce(void *bp);
static void insert_node(void *bp);
static void delete_node(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Heap check header */
int mm_check(void);

/* Helper functions */

/*
* Extend heap: extends heap by aligned number of bytes, coalescing as needed and modifying segregated list
*/
static void *extend_heap(size_t words)
{
    char *bp;                   
    size_t size;
    
    size = ALIGN(words);
    
    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;
    
    // Set headers and footer 
    WRITE(HEADER(bp), PACK(size, 0));  
    WRITE(FOOTER(bp), PACK(size, 0));   
    WRITE(HEADER(NEXT(bp)), PACK(0, 1)); 
    insert_node(bp); //need to insert new node into the right free list
    
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
* Coalesce: combines a free block with free blocks next to it in physical memory, modifying segregated list as needed
*/
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(HEADER(PREVIOUS(bp)));
    size_t next_alloc = GET_ALLOC(HEADER(NEXT(bp)));
    size_t size = GET_SIZE(HEADER(bp));
    

    if (prev_alloc && next_alloc) {                         // Case 1
        return bp;
    }
    else if (prev_alloc && !next_alloc) {                   // Case 2
        delete_node(bp); //need to delete nodes from free list
        delete_node(NEXT(bp));
        size += GET_SIZE(HEADER(NEXT(bp)));
        WRITE(HEADER(bp), PACK(size, 0));
        WRITE(FOOTER(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {                 // Case 3 
        delete_node(bp);
        delete_node(PREVIOUS(bp));
        size += GET_SIZE(HEADER(PREVIOUS(bp)));
        WRITE(FOOTER(bp), PACK(size, 0));
        WRITE(HEADER(PREVIOUS(bp)), PACK(size, 0));
        bp = PREVIOUS(bp);
    } else {                                                // Case 4
        delete_node(bp);
        delete_node(PREVIOUS(bp));
        delete_node(NEXT(bp));
        size += GET_SIZE(HEADER(PREVIOUS(bp))) + GET_SIZE(HEADER(NEXT(bp)));
        WRITE(HEADER(PREVIOUS(bp)), PACK(size, 0));
        WRITE(FOOTER(NEXT(bp)), PACK(size, 0));
        bp = PREVIOUS(bp);
    }
    
    insert_node(bp); //put newly coalesced node into correct free list
    
    return bp;
}

/*
* Insert_node: Places a node on the appropriate segregated list, and keeps the list sorted by ascending size
* Each segregated list spans values from [2^n, 2^(n+1)) in segregated_free_list[n]
*/
static void insert_node(void *bp) 
{
  int list = 0;
  void *search_ptr = bp;
  void *insert_ptr = NULL;
  size_t size = GET_SIZE(HEADER(bp));
  
  /* Select segregated list */
  while ((list < LISTS - 1) && (size > 1)) {
    size >>= 1;
    list++;
  }
  
  /* Select location on list to insert pointer while keeping list
     organized by byte size in ascending order. To insert after insert_ptr, before search_ptr */
  search_ptr = segregated_free_list[list];
  while ((search_ptr != NULL) && (size > GET_SIZE(HEADER(search_ptr)))) {
    insert_ptr = search_ptr;
    search_ptr = PREDECESSOR(search_ptr);
  }
  
  /* Set predecessor and successor */
  if (search_ptr != NULL) {
    if (insert_ptr != NULL) { //Case 1: middle of list
      SET_PTR(PREDECESSOR(bp), search_ptr); 
      SET_PTR(SUCCESSOR(search_ptr), bp);
      SET_PTR(SUCCESSOR(bp), insert_ptr);
      SET_PTR(PREDECESSOR(insert_ptr), bp);
    } else { //Case 2: beginning of list
      SET_PTR(PREDECESSOR(bp), search_ptr); 
      SET_PTR(SUCCESSOR(search_ptr), bp);
      SET_PTR(SUCCESSOR(bp), NULL);
      
      /* Add block to appropriate list */
      segregated_free_list[list] = bp;
    }
  } else {
    if (insert_ptr != NULL) { //Case 3: end of list
      SET_PTR(PREDECESSOR(bp), NULL);
      SET_PTR(SUCCESSOR(bp), insert_ptr);
      SET_PTR(PREDECESSOR(insert_ptr), bp);
    } else { //Case 4: only item on list
      SET_PTR(PREDECESSOR(bp), NULL);
      SET_PTR(SUCCESSOR(bp), NULL);
      
      /* Add block to appropriate list */
      segregated_free_list[list] = bp;
    }
  }

  return;
}

/*
* delete_node: Removes node from the relevant segregated list
*/
static void delete_node(void *bp) 
{
    int list = 0;
    size_t size = GET_SIZE(HEADER(bp));
    
    // Select segregated list 
    while ((list < LISTS - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
    if (PREDECESSOR(bp) != NULL) {
        if (SUCCESSOR(bp) != NULL) { //Case 1: middle of list
            SET_PTR(SUCCESSOR(PREDECESSOR(bp)), SUCCESSOR(bp));
            SET_PTR(PREDECESSOR(SUCCESSOR(bp)), PREDECESSOR(bp));
        } else { //Case 2: end of list
            SET_PTR(SUCCESSOR(PREDECESSOR(bp)), NULL);
            segregated_free_list[list] = PREDECESSOR(bp);
        }
    } else {
        if (SUCCESSOR(bp) != NULL) { // beginning of list
            SET_PTR(PREDECESSOR(SUCCESSOR(bp)), NULL);
        } else { //Case 4: only item on list
            segregated_free_list[list] = NULL;
        }
    }
    
    return;
}

/*
* find_fit: performs first-fit search of the segregated free list, which is sorted by size
*/
static void *find_fit(size_t asize)
{
    void *bp;
    int list = 0;
    size_t size = asize;
    
    /* Select segregated list */
    while ((list < LISTS - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
    bp = segregated_free_list[list]; //set bp to the appropriate free list
    
    /* Search for first fit on selected list */
    while ((bp != NULL) && (asize > GET_SIZE(HEADER(bp)))) {
        bp = PREDECESSOR(bp);
    }
    
    return bp;
}

/*
* place: puts the requested block at the beginning of the located free block, splitting iff the remainder >= min block size
*/
static void place(void *bp, size_t asize)
{
    size_t size = GET_SIZE(HEADER(bp));
    
    delete_node(bp); //remove from free list
    
    if ((size - asize) >= MINBLOCK) { //Case 1: split
        WRITE(HEADER(bp), PACK(asize, 1));
        WRITE(FOOTER(bp), PACK(asize, 1));
        bp = NEXT(bp);
        WRITE(HEADER(bp), PACK(size-asize, 0));
        WRITE(FOOTER(bp), PACK(size-asize, 0));
        insert_node(bp); //add new node to free list
    }
    else { //Case 2: don't split
        WRITE(HEADER(bp), PACK(size, 1));
        WRITE(FOOTER(bp), PACK(size, 1));
    }
    
    return;
}

/*
* mm_check: checks the heap for the following, returns 0 if errors and 1 otherwise:
* are all items in free list marked as free?
* are the prologue and epilogue blocks correct?
*/
int mm_check(void)
{
    int check = 1; //set default return, no errors
    void *bp; 
    void *current;
    size_t size;
    int list = 0;
    int found;
    
    /* Check the segregated free list to ensure all entries are free */
    while (list < LISTS) { //scan through each free list
        bp = segregated_free_list[list];
	list++;
        while (bp != NULL) {
            if (GET_ALLOC(bp)) { //if list is allocated, error and break to next segregated list
                check = 0;
                printf("Error: free list %d contains allocated block(s)\n", list);
                break;
            }
            bp = PREDECESSOR(bp);
        }
    }
    
    /* Check prologue header */
    if ((GET_SIZE(HEADER(heap_start)) != DSIZE) || !GET_ALLOC(HEADER(heap_start))) {
        check = 0;
	printf("Bad prologue header\n");
    }
    
    /* Check user blocks */
    bp = heap_start;
    size = GET_SIZE(HEADER(bp));
    while (size > 0) {
        /* 
        * add checks for:
        * are there contiguous free blocks? (i.e. blocks that should have been coalesced)
        * are there overlapping allocated blocks?
        */
	size = GET_SIZE(HEADER(bp));
        if (!GET_ALLOC(HEADER(bp))) { //the checks for free blocks
		/* Check 1: are all free blocks in the correct free list? */
		list = 0;
		while ((list < LISTS - 1) && (size > 1)) { //select correct free list
    			size >>= 1;
    			list++;
  		}
		current = segregated_free_list[list];
		found = 0;
		while (current != NULL) { //scan the free list for the node
			if (current == bp) { //found desired node; break from loop
				found = 1;
				break;
			}
    			current = PREDECESSOR(current);
  		}
		if (!found) { //if it wasn't found, report error
			check = 0;
			printf("Block not in correct free list\n");
		}
	}
	bp = NEXT(bp);
    }
    
    /* Check epilogue header */
    if ((GET_SIZE(HEADER(bp)) != 0) || !(GET_ALLOC(HEADER(bp)))) {
        check = 0;
	printf("Bad epilogue header\n");
    }
    
    return check;
}

/* 
 * mm_init - initialize the malloc package. Returns -1 if problem, 0 otherwise
 */
int mm_init(void)
{
    int list;
    char *start; //pointer to beginning of heap
    
    /* Initialize segregated free list */
    for (list = 0; list < LISTS; list++) {
        segregated_free_list[list] = NULL;
    }
    
    /* Obtained from textbook page 858 */
    
    /* Create initial empty heap */
    if ((start = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    WRITE(start, 0);                              // Alignment padding
    WRITE(start + (1*WSIZE), PACK(DSIZE, 1)); // Prologue header
    WRITE(start + (2*WSIZE), PACK(DSIZE, 1)); // Prologue footer
    WRITE(start + (3*WSIZE), PACK(0, 1));    // Epilogue header
    heap_start = start + DSIZE; //heap starts past prologue header
    
    /* Extend empty heap with free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    
    /* End obtained from textbook */
    
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    //int newsize = ALIGN(size + SIZE_T_SIZE);
    //size_t newsize = (ALIGN(size) + ALIGNMENT) // align size and add space for header  

    /*ignore spurious request*/
    if (size == 0)
        return NULL;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    /* void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr; 
    */
    return ptr;
}














