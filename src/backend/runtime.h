#ifndef __SLL_RUNTIME_H_
#define __SLL_RUNTIME_H_

#include <stddef.h>
#include <inttypes.h>

#define SLL_MAX_OBJECT_SIZE 15

typedef uintptr_t Word;
typedef Word *Object;
typedef Word const CtrId;

#define SLL_make_header(ctr_id, object_size) \
  (((object_size) << 18) | ((ctr_id) & 0xFFFF))

#define SLL_get_ctr_id(header) \
  ((CtrId)((header) & 0xFFFF))

#define SLL_get_osize(header) \
  ((size_t)((header) >> 18))

#define SLL_get_color(header) \
  ((signed char)(((header) >> 16) & 0x3))

#define SLL_set_color(header, color) \
   ((header) | ((unsigned int)((color) & 0x3) << 16))

struct RootsBlock {
  struct RootsBlock *const next;
  size_t const size;
};

extern struct RootsBlock *sll_roots;
extern Word *sll_free_cell[SLL_MAX_OBJECT_SIZE];

void sll_fatal_error(char const *message);
Word *sll_allocate_object(size_t object_size);
void sll_print_value(Object value, char const *const *ctr_names);
void sll_finalize();

#endif  // __SLL_RUNTIME_H_
