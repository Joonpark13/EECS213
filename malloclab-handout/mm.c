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

#include <assert.h>

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

/* single word (8) or double word (16) */
#define ALIGNMENT 8
#define WSIZE 8 //word size, headers and footers
#define DSIZE 16 //double word size
#define LISTS 20 //number of free lists
#define CHUNKSIZE (1<<12)
#define PTRSIZE 8
#define MINBLOCK (DSIZE + (PTRSIZE * 2)) //minimum block size (two pointers + 8 byte headers and footers)

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
#define HEADER(bp) (((char *)(bp)) - WSIZE)
#define FOOTER(bp) (((char *)(bp)) + GET_SIZE(HEADER(bp)) - DSIZE)

/* Given block ptr bp, compute address of (physically) next and previous blocks */
#define NEXT(bp) (((char *)(bp)) + GET_SIZE((char *)(bp) - WSIZE))
#define PREVIOUS(bp) (((char *)(bp)) - GET_SIZE((char *)(bp) - DSIZE))

/* end macros from textbook*/

/* Given block ptr bp, compute address of predecessor and successor ptrs */
#define PREDECESSOR_PTR(bp) (char *)(bp)
#define SUCCESSOR_PTR(bp) (((char *)(bp)) + PTRSIZE)


/* Given block ptr bp, compute address of predecessor and successor */
#define PREDECESSOR(bp) (*(char **)(bp))
#define SUCCESSOR(bp) (*(char **)(SUCCESSOR_PTR(bp)))

// Store predecessor or successor pointer for free blocks; works like write but ensures casting 
#define SET_PTR(p, val) (*(uintptr_t *)(p) = (uintptr_t)(val))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


//#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Global variables */
char *heap_start;

/* Helper function headers */
static void *extend_heap(size_t size);
static void *coalesce(void *bp);
static void insert_node(void *bp);
static void delete_node(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *access_list(int read, int index, void *ptr);

/* Heap check header */
int mm_check(void);

/* Helper functions */

/*
* Extend heap: extends heap by aligned number of bytes, coalescing as needed and modifying segregated list
*/
static void *extend_heap(size_t bytes) {
    char *bp;                   
    size_t size;
    
    size = ALIGN(bytes);
    
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
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(HEADER(PREVIOUS(bp)));
    size_t next_alloc = GET_ALLOC(HEADER(NEXT(bp)));
    size_t size = GET_SIZE(HEADER(bp));
    

    if (prev_alloc && next_alloc) {                         // Case 1
        return bp;
    } else if (prev_alloc && !next_alloc) {                   // Case 2
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
 * Each segregated list spans values from [2^n, 2^(n+1)) in segregated_free_list + PTRSIZE * n
 */
static void insert_node(void *bp) {
    int list = 0;
    void *search_ptr;
    void *insert_ptr = NULL;
    size_t size = GET_SIZE(HEADER(bp));

    /* Select segregated list */
    while ((list < LISTS - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    size = GET_SIZE(HEADER(bp));


    /* Select location on list to insert pointer while keeping list
     organized by byte size in ascending order. To insert after insert_ptr, before search_ptr */
    search_ptr = access_list(1, list, NULL);
    while ((search_ptr != NULL) && (size > GET_SIZE(HEADER(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = PREDECESSOR(search_ptr);
    }

    /* Set predecessor and successor */
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) { //Case 1: middle of list
          SET_PTR(PREDECESSOR_PTR(bp), search_ptr); 
          SET_PTR(SUCCESSOR_PTR(search_ptr), bp);
          SET_PTR(SUCCESSOR_PTR(bp), insert_ptr);
          SET_PTR(PREDECESSOR_PTR(insert_ptr), bp);
        } else { //Case 2: beginning of list
          SET_PTR(PREDECESSOR_PTR(bp), search_ptr); 
          SET_PTR(SUCCESSOR_PTR(search_ptr), bp);
          SET_PTR(SUCCESSOR_PTR(bp), NULL);
          
          /* Add block to appropriate list */
          assert(access_list(1, list, NULL) == search_ptr);
          access_list(0, list, bp);
        }
    } else {
        if (insert_ptr != NULL) { //Case 3: end of list
          SET_PTR(PREDECESSOR_PTR(bp), NULL);
          SET_PTR(SUCCESSOR_PTR(bp), insert_ptr);
          SET_PTR(PREDECESSOR_PTR(insert_ptr), bp);
        } else { //Case 4: only item on list
          SET_PTR(PREDECESSOR_PTR(bp), NULL);
          SET_PTR(SUCCESSOR_PTR(bp), NULL);
          
          /* Add block to appropriate list */
          assert(access_list(1, list, NULL) == search_ptr);
          access_list(0, list, bp);
        }
    }

    return;
}

/*
 * delete_node: Removes node from the relevant segregated list
 */
static void delete_node(void *bp) {
    int list = 0;
    size_t size = GET_SIZE(HEADER(bp));
    
    // Select segregated list 
    while ((list < LISTS - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
   
    if (PREDECESSOR(bp) != NULL) {
        if (SUCCESSOR(bp) != NULL) { //Case 1: middle of list
            SET_PTR(SUCCESSOR_PTR(PREDECESSOR(bp)), SUCCESSOR(bp));
            SET_PTR(PREDECESSOR_PTR(SUCCESSOR(bp)), PREDECESSOR(bp));
        } else { //Case 2: end of list
            SET_PTR(SUCCESSOR_PTR(PREDECESSOR(bp)), NULL);
            assert(access_list(1, list, NULL) == bp);
            access_list(0, list, PREDECESSOR(bp));
        }
    } else {
        if (SUCCESSOR(bp) != NULL) { // beginning of list
            SET_PTR(PREDECESSOR_PTR(SUCCESSOR(bp)), NULL);
        } else { //Case 4: only item on list
            assert(access_list(1, list, NULL) == bp);
            access_list(0, list, NULL);
        }
    }
    
    return;
}

/*
 * find_fit: performs first-fit search of the segregated free list, which is sorted by size
 */
static void *find_fit(size_t asize) {
    void *bp; // Block Pointer
    int list = 0;
    size_t size = asize;
    
    /* Select segregated list */
    while ((list < LISTS - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    while (list < LISTS - 1) {
        // Set bp to the appropriate free list
        bp = access_list(1, list, NULL);
        
        /* Search for first fit on selected list */
        while ((bp != NULL) && (asize > GET_SIZE(HEADER(bp)))) {
            bp = PREDECESSOR(bp);
        }

        if (bp != NULL) {
            assert(GET_SIZE(HEADER(bp)) >= asize);
            return bp;
        }

        list++; // If no free block of appropriate size is found, search the next list
    }
    return NULL;
}

/*
* place: puts the requested block at the beginning of the located free block, splitting iff the remainder >= min block size
*/
static void place(void *bp, size_t asize) {
    size_t size = GET_SIZE(HEADER(bp));
    
    delete_node(bp); // Remove from free list
    
    if ((size - asize) >= MINBLOCK) { // Case 1: split
        WRITE(HEADER(bp), PACK(asize, 1));
        WRITE(FOOTER(bp), PACK(asize, 1));
        bp = NEXT(bp);
        WRITE(HEADER(bp), PACK(size - asize, 0));
        WRITE(FOOTER(bp), PACK(size - asize, 0));
        insert_node(bp); // Add new node to free list
    }
    else { // Case 2: don't split
        WRITE(HEADER(bp), PACK(size, 1));
        WRITE(FOOTER(bp), PACK(size, 1));
    }
    
    return;
}

/*
 * access: reads and writes from the segregated free list, stored as a static array only ever accessed within this function
 * it must always return a pointer however, leading to some stylistic difficulties that could be avoided with the use of a global array
 */
static void *access_list(int read, int index, void *ptr) {
    assert(index < LISTS);
    static void *segregated_free_list[LISTS] = { NULL }; // initialize the free list: occurs only once, values remain same for program life

    if (read) { // read, so return value at index
        return segregated_free_list[index];
    }

    segregated_free_list[index] = ptr; // write, so set value at index to the correct pointer
    return NULL;
}

/*
* mm_check: checks the heap for the following, returns 0 if errors and 1 otherwise:
* are all items in free list marked as free?
* are the prologue and epilogue blocks correct?
* are all free blocks in the correct free list?
* are the contiguous free blocks that should have been coalesced?
*/
int mm_check(void) {
    int check = 1; //set default return, no errors
    void *bp; 
    void *current;
    size_t size;
    int list = 0;
    int found;
    
    /* Check the segregated free list to ensure all entries are free */
    while (list < LISTS) { //scan through each free list
        bp = access_list(1, list, NULL);
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
       	size = GET_SIZE(HEADER(bp));
        if (!GET_ALLOC(HEADER(bp))) { //the checks for free blocks
		/* Check 1: are all free blocks in the correct free list? */
		list = 0;
		while ((list < LISTS - 1) && (size > 1)) { //select correct free list
    			size >>= 1;
    			list++;
  		}
                current = access_list(1, list, NULL);
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
		/* Check 2: Are there contiguous free blocks that should have been coalesced? */
		if (!GET_ALLOC(HEADER(NEXT(bp)))) { //if the next block is free
			check = 0;
			printf("Contiguous free blocks that should have been coalesced.\n");
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
int mm_init(void) {
    // Clear all values in our segregated free list
    int i;
    for (i = 0; i < LISTS; i++) {
        access_list(0, i, NULL);
    }

    char *start;
    
    /* Obtained from textbook page 858 */
    
    /* Create initial empty heap */
    if ((start = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    WRITE(start, 0);                              // Alignment padding
    WRITE(start + (1 * WSIZE), PACK(DSIZE, 1)); // Prologue header
    WRITE(start + (2 * WSIZE), PACK(DSIZE, 1)); // Prologue footer
    WRITE(start + (3 * WSIZE), PACK(0, 1));    // Epilogue header
    heap_start = start + DSIZE; //heap starts past prologue header
    
    /* Extend empty heap with free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE) == NULL)
        return -1;
    
    /* End obtained from textbook */
    
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    // Ignore suprious requests.
    if (size == 0)
        return NULL;

    size_t adj_size;

    if (size <= DSIZE) {
        adj_size = MINBLOCK;
    } else {
        adj_size = ALIGN(size+DSIZE);
    }
    
    void *bp = find_fit(adj_size);

    if (bp != NULL) {
        place(bp, adj_size);
        return bp;
    }

    size_t extend_size = MAX(adj_size, CHUNKSIZE);
    if ((bp = extend_heap(extend_size)) == NULL)
        return NULL; // In case of error
    place(bp, adj_size);
    return bp;
}

/*
 * mm_free - 
 */
void mm_free(void *ptr) {
    if (GET_ALLOC(HEADER(ptr))) { //only free allocated blocks
    	size_t size = GET_SIZE(HEADER(ptr));

    	WRITE(HEADER(ptr), PACK(size, 0));
    	WRITE(FOOTER(ptr), PACK(size, 0));
	
    	insert_node(ptr);
    	coalesce(ptr);
    }
    return;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    // If input size is equal to current size of block,
    // return the same pointer (suprious request)
    //
    // If input size is smaller than current size of block,
    // shrink size of block, add remaining free block to corresponding SFL
    // return the same pointer
    //
    // If input size is greater, check if the block directly after or before it (in mem space) has enough space to accomodate.
    // If so, un-coalesce with relevant block, return relevant pointer.
    //
    // If not, use free and malloc to re-allocate space somewhere else.
    return 0;
}

