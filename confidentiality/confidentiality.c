#include "confidentiality.h"

struct Page* pages;
unsigned user_level;

/**
 * Memory initialization. Every page has a NULL address and 0 conf level.
 * Should be called at the beginning of main (or ideally before).
 */
int init() {
	pages = malloc(MAX_PAGE_NB * sizeof(struct Page));
	if(pages == NULL)
		return 0;
	/*@
		loop invariant 0 <= i <= MAX_PAGE_NB;
		loop invariant \forall unsigned j; 0 <= j < i ==>
			pages[j].status == PAGE_FREE && pages[j].confidentiality_level == 0;
	*/
	for(unsigned i = 0 ; i < MAX_PAGE_NB ; ++i) {
		char* p = malloc(PAGE_SIZE * sizeof(char));
		if(p == NULL)
			return 0;
		else {
			pages[i].status = PAGE_FREE;
			memset(p, 0, PAGE_SIZE * sizeof(char));
			pages[i].confidentiality_level = 0;
			pages[i].data = p;
		}
	}
	user_level = 0;
	return 1;
}

/**
 * Returns the first free page it finds or NULL
 */
struct Page* find_free_page() {
	/*@
		loop invariant 0 <= i <= MAX_PAGE_NB;
	*/
	for(int i = 0 ; i < MAX_PAGE_NB ; ++i)
		if(pages[i].status == PAGE_FREE)
			return pages + i;
	return NULL;
}

/* Example : Caesar encryption
void encrypt(char* data, unsigned key, unsigned size) {
	for(int i = 0 ; i < size ; ++i)
		data[i] = (data[i] + key) % 128;
}
void decrypt(char* data, unsigned key, unsigned size) {
	for(int i = 0 ; i < size ; ++i)
		data[i] = (data[i] - key) % 128;
}
*/

/**
 * Allocates a new page (if there is memory still available) and returns it
 * Its confidentiality level is the current level of the caller.
 */
struct Page* page_alloc() {
	struct Page* fp = find_free_page();
	/*@
		loop invariant 0 <= i <= MAX_PAGE_NB;
		loop invariant \forall unsigned j; 0 <= j < i ==>
			pages[j].status != PAGE_FREE;
		loop assigns i;
	*/
	for(unsigned i = 0 ; i < MAX_PAGE_NB ; ++i)
		if(pages[i].status == PAGE_FREE) {
			pages[i].confidentiality_level = user_level;
			pages[i].status = PAGE_ALLOCATED;
			return pages + i;
		}
	return NULL;
}

/**
 * Free a page and erase its content
 * (replacing it by zeroes).
 * No effect if the page is already free.
 */
void page_free(struct Page* p) {
	if(p != NULL && p->status == PAGE_ALLOCATED) {
		memset(p->data, 0, PAGE_SIZE * sizeof(char));
		p->status = PAGE_FREE;
	}
}

/**
 * Copies PAGE_LENGTH bytes from 'from's data to the buffer
 * if the confidentiality conditions are met
 */
int page_read(struct Page* from, char* buffer) {
	if(from != NULL && from->status == PAGE_ALLOCATED &&
		from->confidentiality_level <= user_level) {
		memcpy(buffer, from->data, PAGE_SIZE);
		return PAGE_OK;
	} else return PAGE_ERROR;
}

/**
 * Copies PAGE_LENGTH bytes from the buffer data to 'to's data
 * if the confidentiality conditions are met
 */
int page_write(struct Page* to, char* buffer) {
	if(to != NULL && to->status == PAGE_ALLOCATED &&
		to->confidentiality_level >= user_level) {
		memcpy(to->data, buffer, PAGE_SIZE);
		return PAGE_OK;
	} else return PAGE_ERROR;
}

/**
 * Raise the confidentiality level if the correct key is passed
 */
unsigned raise_conf_level() {
	return ++user_level;
}

/**
 * Lower the confidentiality level
 */
unsigned lower_conf_level() {
	if(user_level > 0)
		--user_level;
	return user_level;
}

/**
 * Encrypt the given page in place (using the encrypt primitive)
 * if the confidentiality conditions are met, effectively lowering
 * its confidentiality level to 0
 */
int page_encrypt(struct Page* p) {
	if(p != NULL && p->confidentiality_level > 0
			&& p->confidentiality_level == user_level
			&& p->status == PAGE_ALLOCATED) {
		encrypt(p->data, user_level, PAGE_SIZE);
		p->encrypted_level = user_level;
		p->confidentiality_level = 0;
		return PAGE_OK;
	}
	else return PAGE_ERROR;
}

/**
 * Decrypt the given page in place (using the decrypt primitive)
 * if the confidentiality conditions are met, effectively restoring
 * its previous confidentiality level
 */
int page_decrypt(struct Page* p) {
	if(p != NULL && p->confidentiality_level == 0
			&& p->encrypted_level == user_level
			&& p->status == PAGE_ALLOCATED) {
		p->confidentiality_level = user_level;
		decrypt(p->data, user_level, PAGE_SIZE);
		return PAGE_OK;
	}
	else return PAGE_ERROR;
}
