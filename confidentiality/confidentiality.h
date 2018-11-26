#include <stdlib.h>
#include <string.h>

/*
	CONFIDENTIALITY EXAMPLE
	
	We model a confidentiality-oriented page manager as described in the paper.

	To that we add simple encryption management, where an authorized user can
	encrypt a page inplace, thus lowering its confidentiality to 0, and decrypt
	an encrypted page, restoring its previous confidentiality level.
	This is modelized by unimplemented (but specified) encrypt/decrypt
	primitives and API functions building on them.

	The goal was to write an API of small functions, and to specify it with the
	following meta-properties:

	- Never write to a lower confidentiality page
	- Never read from a higher confidentiality page
	- Page status is only modified in page_alloc/init/free
	- Free pages are not written upon
	- Free pages are not read from
	- The content of a free page is always null
	- The confidentiality of an allocated page is constant outside of encrypt/decrypt
	- The encryption level is constant outside of encrypt/decrypt

	Each function in the API was minimally specified with function contracts so
	as the proof of the meta-properties to succeed.
*/

#define MEMORY_SIZE 0x10000
#define PAGE_SIZE ((unsigned)0x100)
#define MAX_PAGE_NB (MEMORY_SIZE / PAGE_SIZE)

#define PAGE_OK 0
#define PAGE_ERROR 1

enum allocation_status {PAGE_ALLOCATED, PAGE_FREE};

//Struct for page metadata
struct Page {
	char* data; //First address of the page
	enum allocation_status status; //Allocation status
	unsigned confidentiality_level; //Confidentiality level of the page
	unsigned encrypted_level; //Remember the previous confidentiality when encrypting
};

//Global metadata array (of size MAX_PAGE_NB)
extern struct Page* pages;

//Current confidentiality level of the agent
extern unsigned user_level;

//Useful predicates for specification purposes
/*@
	predicate valid_page(struct Page* p) =
		\valid(p) && \valid(p->data + (0 .. PAGE_SIZE - 1)) &&
		\exists int i; 0 <= i < MAX_PAGE_NB && p == pages + i;

	//The given page is filled with zeroes
	predicate clean_page(struct Page* p) =
			\forall int i; 0 <= i < PAGE_SIZE ==>
				p->data[i] == 0;
*/

/*@
	ensures \result ==> \forall int i; 0 <= i < MAX_PAGE_NB ==>
		pages[i].status == PAGE_FREE && pages[i].confidentiality_level == 0;
	ensures \result ==> user_level == 0;
*/
int init();

struct Page* page_alloc();

/*@
	behavior valid:
		assumes p != \null;
		requires valid_page(p);
*/
void page_free(struct Page* p);

/*@
	behavior valid:
		assumes from != \null;
		requires valid_page(from);
		requires \valid(buffer + (0 .. PAGE_SIZE - 1));
		//Buffer unrelated to page fields (status_constant)
		requires \forall int i; 0 <= i < MAX_PAGE_NB ==>
			\separated(pages + i, buffer + (0 .. PAGE_SIZE - 1));
		//Buffer unrelated to pages data (memcpy)
		requires \forall int i; 0 <= i < MAX_PAGE_NB ==>
			\separated(pages[i].data + (0 .. PAGE_SIZE - 1),
					buffer + (0 .. PAGE_SIZE - 1));
*/
int page_read(struct Page* from, char* buffer);

/*@
	behavior valid:
		assumes to != \null;
		requires valid_page(to);
		requires \valid(buffer + (0 .. PAGE_SIZE - 1));
		//'to' data unrelated to page fields (status_constant)
		requires \forall int i; 0 <= i < MAX_PAGE_NB ==>
			\separated(pages + i, to->data + (0 .. PAGE_SIZE - 1));
		//Buffer unrelated to page data (memcpy)
		requires \forall int i; 0 <= i < MAX_PAGE_NB ==>
			\separated(pages[i].data + (0 .. PAGE_SIZE - 1),
					buffer + (0 .. PAGE_SIZE - 1));
*/
int page_write(struct Page* to, char* buffer);

unsigned raise_conf_level();

unsigned lower_conf_level();

/*@
	assigns *(data + (0 .. size - 1)) \from *(data + (0 .. size - 1));
*/
void encrypt(char* data, unsigned key, unsigned size);

/*@
	assigns *(data + (0 .. size - 1)) \from *(data + (0 .. size - 1));
*/
void decrypt(char* data, unsigned key, unsigned size);

/*@ 
	behavior valid:
		assumes p != \null;
		requires valid_page(p);
*/
int page_encrypt(struct Page* p);
/*@ 
	behavior valid:
		assumes p != \null;
		requires valid_page(p);
*/
int page_decrypt(struct Page* p);


/*@ // Reasonable memory hypotheses as axioms
	axiomatic memory_separation {
		axiom all_sep: \forall struct Page* p; valid_page(p) ==>
			\forall int i; 0 <= i < MAX_PAGE_NB &&  pages + i != p ==>
				\separated(p->data + (0 .. PAGE_SIZE - 1),
						pages[i].data + (0 .. PAGE_SIZE - 1));

		axiom local_sep: \forall int i,j;
			0 <= i < MAX_PAGE_NB ==>
			0 <= j < MAX_PAGE_NB ==> \let p = pages + j;
			\separated(&pages[i].confidentiality_level, p->data + (0 .. PAGE_SIZE - 1)) &&
			\separated(&pages[i].status, p->data + (0 .. PAGE_SIZE - 1)) &&
			\separated(&(pages[i]).data, p->data + (0 .. PAGE_SIZE - 1));

		axiom local_sep2: \forall int i, j;
			0 <= i < MAX_PAGE_NB ==>
			0 <= j < MAX_PAGE_NB ==> \let p = pages + j;
			\separated(&pages[i].encrypted_level, p->data + (0 .. PAGE_SIZE - 1));
	}

*/

//========================== METAPROPERTIES ====================

/*@
	//Page status is only modified in page_alloc/init/free
	meta status_constant: \forall function f;
			! \subset(f, {\f(init), \f(page_alloc), \f(page_free)}) ==> \writing(f),
			\forall int i; 0 <= i < MAX_PAGE_NB ==> \let p = pages + i;
			\separated(\written, &p->status);
*/

/*@
	//Never write to a lower confidentiality page outside of free
	meta confidential_write: \forall function f;
		! \subset(f, {\f(page_free), \f(init)}) ==>
		\writing(f),
		\forall int i; 0 <= i < MAX_PAGE_NB ==>
		\let p = pages + i;
		p->status == PAGE_ALLOCATED ==>
		user_level > p->confidentiality_level ==>
		\separated(\written, p->data + (0.. PAGE_SIZE - 1));
*/

/*@
	//Never read from a higher confidentiality page
	meta confidential_read: \forall function f;
		\reading(f),
		\forall int i; 0 <= i < MAX_PAGE_NB ==>
		\let p = pages + i;
		p->status == PAGE_ALLOCATED ==>
		user_level < p->confidentiality_level ==>
		\separated(\read, p->data + (0.. PAGE_SIZE - 1));
*/

/*@
	//Free pages are not written upon
	meta constant_free_pages: \forall function f;
		!\subset(f, \f(init)) ==> \writing(f),
		\forall unsigned i;
		0 <= i < MAX_PAGE_NB ==>
		pages[i].status == PAGE_FREE ==>
			\separated(\written, pages[i].data + (0 .. PAGE_SIZE - 1));
*/

/*@
	//Free pages are not read from
	meta hidden_free_pages: \forall function f;
		!\subset(f, \f(init)) ==> \reading(f),
		\forall unsigned i;
		0 <= i < MAX_PAGE_NB ==> pages[i].status == PAGE_FREE ==>
		\separated(\read, pages[i].data + (0 .. PAGE_SIZE - 1));
*/

/*@
	//Current confidentiality is only modified through raise/lower_conf_level
	meta \forall function f;
		! \subset(f, {\f(raise_conf_level), \f(lower_conf_level), \f(init)}) ==>
		\writing(f), \separated(\written, &user_level);
*/

/*@
	//Confidentiality modifiers are not called within the library
	meta \forall function f;
		\calling(f),
		\called != (char**) raise_conf_level &&
		\called != (char**) lower_conf_level;
*/

/*@
	//The content of a free page is always null
	meta free_page_null: \forall function f; !\subset(f, \f(init)) ==>
		\strong_invariant(f),
		\forall unsigned i; 0 <= i < MAX_PAGE_NB ==>
			pages[i].status == PAGE_FREE ==> clean_page(pages + i);
*/

/*@
	//The confidentiality of an allocated page is constant outside of encrypt/decrypt
	meta constant_conf_level: \forall function f;
		! \subset(f, {\f(init), \f(page_encrypt), \f(page_decrypt)}) ==>
		\writing(f),
		\forall unsigned i; 0 <= i < MAX_PAGE_NB ==>
		pages[i].status == PAGE_ALLOCATED ==>
		\separated(\written, &pages[i].confidentiality_level);
*/

/*@
	//The encryption level is constant outside of encrypt/decrypt
	meta constant_enc_level: \forall function f;
		! \subset(f, {\f(init), \f(page_encrypt), \f(page_decrypt)}) ==>
		\writing(f),
		\forall unsigned i; 0 <= i < MAX_PAGE_NB ==>
		\separated(\written, &pages[i].encrypted_level );
*/

/*@
	//The encryption/decryption primitives are only called within page_encrypt
	//and page_decrypt
	meta encdec_uncalled: \forall function f;
		! \subset(f, {\f(page_encrypt), \f(page_decrypt)}) ==> \calling(f),
		\called != (char**)encrypt && \called != (char**)decrypt;
*/
