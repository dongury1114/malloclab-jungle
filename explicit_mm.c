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
    "team 7",
    /* First member's full name */
    "donggyu lee",
    /* First member's email address */
    "dongury1114@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};



/* single word(4) or double word (8) alignment */
/* 아래 ALIGH(size) 함수에서 할당할 크기인 size를 8의 배수로 맞춰서 할당하기 위한 매크로 */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
/* 할당할 크기인 size를 보고 8의 배수 크기로 할당하기 위해 size를 다시 align하는 작업을 한다. 만약 size가 4이면 (4+8-1) = 11 = 0000 1011 이고
이를 ~0x7 = 1111 1000과 AND 연한하면 0000 1000 = 8이 되어 적당한 8의 배수 크기로 align할 수 있다.*/
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* 메모리 할당 시 기본적으로 header와 footer를 위해 필요한 더블워드만큼의 메모리 크기.
    long형인 size_t의 크기만큼 8을 나타내는 매크로.
 */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
기본 상수와 매크로
*/

/* 기본 단위인 word, double word, 새로 할당받는 힙 크기 CHUNKSIZE를 정의 */

#define WSIZE 4 /* word와 header/footer 사이즈 */
#define DSIZE 8 /* Double word size (bytes) */
#define MINIMUM 16 /* initial prologue 블록 사이즈, header, footer, PREC, SUCC 포인터 */
#define CHUNKSIZE (1<<12) /* 힙을 1<<12만큼 연장 => 4096byte */

#define MAX(x, y) ((x) > (y) ? (x) : (y)) //최댓값 구하는 함수 매크로

/* header 및 footer 값 (size + allocated) 리턴 */
#define PACK(size, alloc) ((size) | (alloc))

/* 주소 p에서의 word를 읽어오거나 쓰는 함수 */
#define GET(p) (*(unsigned int*)(p))
#define PUT(p, val) (*(unsigned int*)(p) = (val)) // 주소 p에 val을 넣어준다.

/* header or footer에서 블록의 size, allocated field를 읽어온다 */
#define GET_SIZE(p) (GET(p) & ~0x7) /* GET(p)로 읽어오는 주소는 8의 배수 & 이를 7을 뒤집은 1111 1000과 AND 연산하면 정확히 블록 크기(뒷 세자리는 제외)만 읽어오기 가능*/
#define GET_ALLOC(p) (GET(p) & 0x1) /* 0000 0001과 AND 연산 => 끝자리가 1이면 할당/0이면 해제 */

/* 블록 포인터 bp를 인자로 받아 블록의 header와 footer의 주소를 반환 */
#define HDRP(bp) ((char*)(bp)-WSIZE) /* 헤더 포인터: bp의 주소를 받아서 한 워드 사이즈 앞으로 가면 헤더가 있음.*/
#define FTRP(bp) ((char*)bp + GET_SIZE(HDRP(bp)-DSIZE)) 
/*footer 포인터: 현재 블록 포인터 주소에서 전체 사이즈만큼 더해주고(전체 사이즈 알려면 HDRP(bp)로 전체 사이즈 알아내야) 맨앞 패딩 + header만큼 빼줘야 footer를 가리킨다. */

/* 블록 포인터 bp를 인자로 받아 이후, 이전 블록의 주소를 리턴 */

#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE((char*)(bp) - WSIZE)) /* 현재 블록 포인터에서 전체 블록 사이즈만큼 더하고 헤더만큼 워드 사이즈 하나 빼면 다음 블록 포인터 */
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE((char*)(bp)-DSIZE)) /* 현재 블록 포인터에서 더블워드만큼 빼면 우리블록 헤더 -> 다음 블록 footer로 가서 사이즈 읽어내기 가능 */

/* Free List 상에서의 이전, 이후 블록 포인터를 리턴 */
/* Free list에서는 bp가 PREC을 가리키고 있고 SUCC는 그 다음 블록을 가리키고 있는 상태 */
#define PREC_FREEP(bp) (*(void**)(bp)) // 이전 블록의 bp에 들어있는 주소값을 리턴
#define SUCC_FREEP(bp) (*(void**)(bp + WSIZE)) // 이후 블록의 bp

/* define searching method for find suitable free blocks to allocate */

// #define NEXT_FIT -> define 하면 next_fit, 안하면 first_fit으로 탐색

/*global variable & functions */

static char* heap_listp = NULL; // 항상 prologue block(힙의 맨앞 시작점)을 가리키는 정적 전역 변수 설정
static char* free_listp = NULL; // free list의 맨 첫 블록을 가리키는 포인터

static void* extend_heap(size_t words); // 주어진 워드 사이즈만큼 힙을 늘린다.
static void* coalesce(void* bp); // 현재 블록 포인터를 인자로 받아 합체
static void* find_fit(size_t asize); // 블록이 들어갈 사이즈 맞는 애를 찾아
static void place(void* bp, size_t newsize); // 새로운 블록을 배치

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *ptr, size_t size);

/* mm_init: 말록 패키지를 초기화 */

int mm_init(void)
{
    /* 메모리에서 6word: 
    1. 더블 워드 경계로 정렬된 미사용 패딩(padding)
    2. 프롤로그 헤더(prol_header)
    3. 프롤로그 블록 안에 prec 포인터를 null로 초기화 -> 이전 블록 가리키는 포인터(PREC)
    4. 프롤로그 블록 안에 succ 포인터를 null로 초기화 -> 다음 블록 가리키는 포인터(SUCC)
    5. 프롤로그 footer(prol_footer)
    6. 에필로그 헤더(epil_header)
    */
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void*)-1) {
       return -1;
    }
    PUT(heap_listp, 0); //alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(MINIMUM, 1));
    PUT(heap_listp + (2*WSIZE), NULL); // prec
    PUT(heap_listp + (3*WSIZE), NULL); // succ
    PUT(heap_listp + (4*WSIZE), PACK(MINIMUM, 1));
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));

    free_listp = heap_listp + 2*WSIZE;

    /* 그 후 CHUNKSIZE만큼 힙을 확장해 초기 가용 블록을 생성 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) 
    { // 실패하면 -1 리턴
        return -1;
    }
    return 0;
}

/*
    coalesce(bp): 해당 가용 블록을 앞뒤 가용블록과 연결하고 연결된 가용 블록의 주소를 리턴
*/

static void* coalesce(void* bp){
    //직전 블록의 footer, 직후 블록의 header를 보고 가용 여부를 확인.
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 직전 블록 가용 여부 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 직후 블록 가용 여부 확인
    size_t size = GET_SIZE(HDRP(bp));


    // case 1: 직전, 직후 블록이 모두 할당 -> 해당 블록만 free list에 넣어준다.

    // case 2: 직전 블록 할당, 직후 블록 가용

    if (prev_alloc && !next_alloc) {
        removeBlock(NEXT_BLKP(bp)); // free 상태였던 직후 블록을 free list에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 3: 직전 블록 가용, 직후 블록 할당
    else if (!prev_alloc && next_alloc){ // alloc이 0이니까  !prev_alloc == True.
        removeBlock(PREV_BLKP(bp)); // 직전 블록을 free list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 4: 직전, 직후 블록 모두 가용
    else if (!prev_alloc && !next_alloc) {
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 앞뒤 free된 블록 전체 사이즈 계산
        bp = PREV_BLKP(bp); // 현재 bp를 가용인 앞쪽 블록으로 이동시켜 => 거기가 전체 free 블록의 앞쪽이 되어야 함.
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // 연결된 새 가용 블록을 free list에 추가
    putFreeBlock(bp);

    return bp;
}

/*
mm_malloc - Allocate a block by incrementing the brk pointer
    Always allocate a block whose size is a multiple of the alignment.
*/

void *mm_malloc(size_t size) {
    size_t asize; // Adjusted block size
    size_t extendsize; // Amount for extend heap if there is no fit
    char* bp;

    // 가짜 요청 spurious request 무시
    if (size == 0) {
        return NULL;
    }
    // 요청 사이즈에 header와 footer를 위한 dword 공간(SIZE_T_SIZE)을 추가한 후 align해준다.
    asize = ALIGN(size + SIZE_T_SIZE);

    // 할당할 가용 리스트를 찾아 필요하다면 분할해서 할당한다.
    if ((bp = find_fit(asize)) != NULL) { // first fit으로 추적.
        place(bp, asize); // 필요하다면 분할하여 할당
        return bp;
    }

    // 만약 맞는 크기의 가용 블록이 없다면 새로 힙을 늘려서 새 힙에 메모리를 할당.
    extendsize = MAX(asize, CHUNKSIZE); // 둘 중 더 큰 값으로 사이즈를 정한다.
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
    extend_heap: 워드 단위 메모리를 인자로 받아 힙을 늘려준다.
*/

static void* extend_heap(size_t words) {
    // 워드 단위로 받는다.
    char* bp;
    size_t size;

    /* 더블 워드 정렬에 따라 메모리를 mem_sbrk 함수를 이용해 할당받음. mem_sbrk는 힙 용량을 늘려줌.*/ 
    size = (words % 2) ? (words + 1) * WSIZE : (words) * WSIZE; // size를 짝수 word && byte 형태로 만든다.
    if ((long)(bp = mem_sbrk(size)) == -1) {// 새 메모리의 첫 부분을 bp로 둔다. 주소값은 int로는 못 받으니 long으로 type casting
    return NULL;
    }
    /* 새 가용 블록의 header와 footer를 정해주고 epliogue block을 가용 블록 맨 끝으로 옮긴다. */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 에필로그 헤더

    /* 만약 이전 블록이 가용 블록이라면 연결 */
    return coalesce(bp);
}

/*
first_fit: 힙의 맨 처음부터 탐색해서 요구하는 메모리 공간보다 큰 가용 블록의 주소를 반환.
*/

static void* find_fit(size_t asize) {
    /* First_fit */
    void* bp;

    // free list의 맨 뒤는 프롤로그 블록이다. free list에서 유일하게 할당된 블록이므로 얘를 만나면 탐색 종료.
    for (bp = free_listp; GET_ALLOC(HDRP(bp))!= 1; bp = SUCC_FREEP(bp)){
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }

    // 못 찾으면 NULL을 리턴한다.
    return NULL;
}

/*
place(bp, size): 요구 메모리를 할당할 수 있는 가용 블록을 할당. 이때, 분할이 가능하면 분할
*/

static void place(void* bp, size_t asize) {
    // 현재 할당할 수 있는 가용 블록 주소

    size_t csize = GET_SIZE(HDRP(bp));

    //할당될 블록이니 free list에서 없애준다.
    removeBlock(bp);

    // 분할 가능한 경우
    if ((csize - asize) >= (2*DSIZE)) {
        // 앞 블록은 할당 블록으로
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // 뒤 블록은 가용 블록으로 분할
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));

        // free list 첫번째에 분할된 블럭을 넣는다.

        putFreeBlock(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
putFreeBlock(bp): 새로 반환되거나 생성된 가용 블록을 free list 첫 부분에 넣는다.
*/

void putFreeBlock(void* bp) {
    SUCC_FREEP(bp) = free_listp;
    PREC_FREEP(bp) = NULL;
    PREC_FREEP(free_listp) = bp;
    free_listp = bp;
}

void removeBlock(void *bp) {
    // Free list의 첫번째 블록 없앨 때
    if (bp == free_listp) {
        PREC_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
    }
    // free list 안에서 없앨 때
    else {
        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
    }
}

/*
mm_free - Freeing a block does nothing.
*/

void mm_free(void *bp) {
    // 해당 블록의 size를 알아내 header와 footer의 정보를 수정.
    size_t size = GET_SIZE(HDRP(bp));

    // header와 footer를 설정

    PUT(HDRP(bp), PACK(size, 0)); // size/0을 헤더에 입력
    PUT(FTRP(bp), PACK(size, 0)); // size/0을 footer에 입력

    // 만약 앞뒤 블록이 가용 상태면 연결
    coalesce(bp);
}

/*
mm_realloc: implimented simply in terms of mm_malloc and mm_free
*/

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr; // 크기를 조절하고 싶은 힙의 시작 포인터
    void *newptr; // 크기 조절 뒤의 새 힙 시작 포인터
    size_t copySize; // 복사할 힙 크기

    newptr = mm_malloc(size);
    if (newptr == NULL) {
        return NULL;
    }

    // copysize: *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));

    // 원래 메모리 크기보다 적은 크기를 realloc하면 크기에 맞는 메모리만 할당되고 나머지는 안 도니다.

    if (size < copySize) {
        copySize = size;
    }

    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}