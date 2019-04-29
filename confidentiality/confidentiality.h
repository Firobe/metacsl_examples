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
	meta \macro,
		\name(\forall_page),
		\arg_nb(2),
		\forall int i; 0 <= i < MAX_PAGE_NB ==>
			\let \param_1 = pages + i; \param_2;

	meta \macro,
		\name(page_data),
		\arg_nb(1),
		\param_1->data + (0 .. PAGE_SIZE - 1);

	meta \macro,
		\name(\constant),
		\arg_nb(1),
		\separated(\written, \param_1);

	meta \macro,
		\name(\hidden),
		\arg_nb(1),
		\separated(\read, \param_1);

	meta \macro,
		\name(not_called),
		\arg_nb(1),
		!\fguard(\called == \param_1);

	logic enum allocation_status page_status(struct Page* p) = p->status;
	logic unsigned page_level(struct Page* p) = p->confidentiality_level;
	predicate page_allocated(struct Page* p) = p->status == PAGE_ALLOCATED;
	predicate page_lower(struct Page* p, unsigned user_level) =
		user_level > p->confidentiality_level;
*/

/*@
	//Page status is only modified in page_alloc/init/free
	meta \prop,
		\name(status_constant),
		\targets(\diff(\ALL, {init, page_alloc, page_free})),
		\context(\writing), \forall_page(p, \constant(&p->status));
*/

/*@
	//Never write to a lower confidentiality page outside of free
	meta \prop,
		\name(confidential_write),
		\targets(\diff(\ALL, {page_free, init})),
		\context(\writing),
			\forall_page(p,
				page_allocated(p) && user_level > page_level(p) ==>
				\constant(page_data(p))
			);
*/

/*@
	//Never read from a higher confidentiality page
	meta \prop,
		\name(confidential_read),
		\targets(\ALL),
		\context(\reading),
			\forall_page(p,
				page_allocated(p) && user_level < page_level(p) ==>
				\hidden(page_data(p))
			);
*/

/*@
	//Free pages are not written upon
	meta \prop,
		\name(constant_free_pages),
		\targets(\diff(\ALL, init)),
		\context(\writing),
			\forall_page(p,
				!page_allocated(p) ==> \constant(page_data(p))
			);
*/

/*@
	//Free pages are not read from
	meta \prop,
		\name(hidden_free_page),
		\targets(\diff(\ALL, init)),
		\context(\reading),
			\forall_page(p,
				!page_allocated(p) ==> \hidden(page_data(p))
			);
*/

/*@
	//Current confidentiality is only modified through raise/lower_conf_level
	meta \prop,
		\name(curconf_wrapped),
		\targets(\diff(\ALL, {raise_conf_level, lower_conf_level, init})),
		\context(\writing), \constant(&user_level);
*/

/*@
	//Confidentiality modifiers are not called within the library
	meta \prop,
		\name(curconf_wrapped_2),
		\targets(\ALL),
		\context(\calling),
			not_called(raise_conf_level) &&
			not_called(lower_conf_level);
*/

/*@
	//The content of a free page is always null
	meta \prop,
		\name(free_page_null),
		\targets(\diff(\ALL, init)),
		\context(\strong_invariant),
			\forall_page(p, !page_allocated(p) ==> clean_page(p));
*/

/*@
	//The confidentiality of an allocated page is constant outside of encrypt/decrypt
	meta \prop,
		\name(constant_conf_level),
		\targets(\diff(\ALL, {init, page_encrypt, page_decrypt})),
		\context(\writing),
			\forall_page(p,
				page_allocated(p) ==> \constant(&p->confidentiality_level)
			);
*/

/*@
	//The encryption level is constant outside of encrypt/decrypt
	meta \prop,
		\name(constant_enc_level),
		\targets(\diff(\ALL, {init, page_encrypt, page_decrypt})),
		\context(\writing),
			\forall_page(p, \constant(&p->encrypted_level));
*/

/*@
	//The encryption/decryption primitives are only called within page_encrypt
	//and page_decrypt
	meta \prop,
		\name(encdec_uncalled),
		\targets(\diff(\ALL, {page_encrypt, page_decrypt})),
		\context(\calling),
			not_called(encrypt) && not_called(decrypt);
*/
