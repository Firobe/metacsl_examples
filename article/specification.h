#include <stdlib.h>

enum allocation { ALLOCATED, FREE };
enum confidentiality { CONFIDENTIAL, PUBLIC };
#define PAGE_NB 256
#define PAGE_LENGTH 1024

struct Page {
	char* data;
	enum allocation status;
	enum confidentiality level;
};

struct Page metadata[PAGE_NB];
enum confidentiality user_level;

struct Page* page_alloc(void);
void page_free(struct Page*);
void page_read(struct Page*, char* buffer);
void page_encrypt(struct Page*);

/*@
	ensures \result == \null
		|| (\exists int page; 0 <= page < PAGE_NB
			&& \result == metadata + page
			&& \result->status == FREE);
	assigns \nothing;
*/
struct Page* find_free_page();

/*@
	meta M1: \forall function f; \strong_invariant(f),
		\forall int page; 0 <= page < PAGE_NB ==>
		metadata[page].status == FREE
		|| metadata[page].status == ALLOCATED;
	meta M2: \forall function f;
		! \subset(f, {\f(page_encrypt)}) ==> \writing(f),
		\forall int page; 0 <= page < PAGE_NB
		&& metadata[page].status == ALLOCATED
		==> \separated(\written, &(metadata[page].level));
	meta M3: \forall function f; \reading(f),
		\forall int page; 0 <= page < PAGE_NB
		&& metadata[page].status == ALLOCATED
		&& user_level == PUBLIC
		&& metadata[page].level == CONFIDENTIAL
		==> \separated(\read, metadata[page].data
			+ (0 .. PAGE_LENGTH - 1));
*/
