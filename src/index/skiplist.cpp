//===----------------------------------------------------------------------===//
//
//                         Peloton
//
// skiplist.cpp
//
// Identification: src/index/skiplist.cpp
//
// Copyright (c) 2015-17, Carnegie Mellon University Database Group
//
//===----------------------------------------------------------------------===//

#include "index/skiplist.h"
#include <stdlib.h>
#include <utility>
#include <iostream>

namespace peloton {
namespace index {
static const int MultiplyDeBruijnBitPosition[32] = {
    0,  1,  28, 2,  29, 14, 24, 3, 30, 22, 20, 15, 25, 17, 4,  8,
    31, 27, 13, 23, 21, 19, 16, 7, 26, 12, 18, 6,  11, 5,  10, 9};

////////////////////////////////////////////////////////////////////
// Interface Method Implementation
////////////////////////////////////////////////////////////////////

SKIPLIST_TEMPLATE_ARGUMENTS
bool SKIPLIST_TYPE::Insert(const KeyType &key, const ValueType &value) {
  // Check whether we should insert the new entry
  void *ptr = Search(key, 0);
  if (!duplicated_key) {
    if (ptr != NULL && key_eq_obj(((LeafNode *)ptr)->pair.first, key))
      return false;
  }

  // Determine the height of the tower
  int v = rand();
  int levels =
      MultiplyDeBruijnBitPosition[((uint32_t)((v & -v) * 0x077CB531U)) >> 27];

  // Fill in keys and values and then link the tower
  LeafNode *lf_node = new LeafNode;
  lf_node->pair = std::make_pair(key, value);

  // in_nodes[i-1] represents an InnerNode at level i
  InnerNode *in_nodes[levels];
  if (levels > 0) {
    for (int i = 0; i < levels; i++) in_nodes[i] = new InnerNode();
    // Link InnerNodes
    for (int i = 1; i < levels; i++) {
      in_nodes[i]->key = key;
      in_nodes[i]->down = in_nodes[i - 1];
    }
    in_nodes[0]->key = key;
    in_nodes[0]->down = lf_node;
  }

// Find the position to insert the key for each level
link_level_0:
  if (ptr == NULL) {
    lf_node->next = head_nodes[0].next;
    while (!__sync_bool_compare_and_swap(&head_nodes[0].next, lf_node->next,
                                         lf_node)) {
      ptr = Search(key, 0);
      goto link_level_0;
    }
  } else {
    lf_node->next = ((LeafNode *)ptr)->next;
    while (!__sync_bool_compare_and_swap(&(((LeafNode *)ptr)->next),
                                         lf_node->next, lf_node)) {
      ptr = Search(key, 0);
      goto link_level_0;
    }
  }

  for (int i = 1; i <= levels; i++) {
  link_level_i:
    void *ptr = Search(key, i);
    if (ptr == NULL) {
      in_nodes[i - 1]->next = head_nodes[i].next;
      while (!__sync_bool_compare_and_swap(
          &head_nodes[i].next, in_nodes[i - 1]->next, in_nodes[i - 1])) {
        goto link_level_i;
      }
    } else {
      in_nodes[i - 1]->next = ((InnerNode *)(ptr))->next;
      while (!__sync_bool_compare_and_swap(&(((InnerNode *)(ptr))->next),
                                           in_nodes[i - 1]->next,
                                           in_nodes[i - 1])) {
        goto link_level_i;
      }
    }
  }
// Add additional levels if the tower exceeds the maximum height
update_max_level:
  int cur_max_level = max_level;
  if (levels > cur_max_level) {
    while (!__sync_bool_compare_and_swap(&max_level, cur_max_level, levels)) {
      goto update_max_level;
    }
  }

  return true;
}

SKIPLIST_TEMPLATE_ARGUMENTS
void SKIPLIST_TYPE::PrintSkipList() {
  for (int i = max_level; i > 0; i--) {
    std::cout << "Level " << i << " :";
    InnerNode *cur = static_cast<InnerNode *>(head_nodes[i].next);
    while (cur != NULL) {
      std::cout << cur->key << "--->";
      cur = static_cast<InnerNode *>(cur->next);
    }
    std::cout << std::endl;
  }
  std::cout << "Level " << 0 << " :";
  LeafNode *cur = static_cast<LeafNode *>(head_nodes[0].next);
  while (cur != NULL) {
    std::cout << "(" << cur->pair.first << ", " << cur->pair.second << ") --->";
    cur = static_cast<LeafNode *>(cur->next);
  }
  std::cout << std::endl;
}

/* It returns the pointer to the node whose key is the largest key <= key at
 * level specified by the input. (It returns a pointer to InnerNode if level
 * > 0 and a pointer to LeafNode if level == 0)
 * If the there is no node before the key at that level, it returns NULL.
 * It returns NULL if level is invalid, meaning level is not in [0,31]
 *
 * NOTE: Even if the max_level is 6, we can still do Search(99, 8) as long
 * as 8 belongs to [0,31]. Of course, it will return NULL because there is
 * no node at level 8 whose key <= 99.
 * */
SKIPLIST_TEMPLATE_ARGUMENTS
void *SKIPLIST_TYPE::Search(const KeyType &key, int level) {
  // Check if skiplist is empty
  if (IsEmpty()) return NULL;
  if (level > max_level || level < 0) return NULL;

  int cur_level = max_level;
  InnerNode *cur = (InnerNode *)head_nodes[cur_level].next;
  void *prev = NULL;
  while (1) {
    if (cur_level == 0) {
      LeafNode *leaf_cur = (LeafNode *)cur;
      while (leaf_cur != NULL && KeyCmpLessEqual(leaf_cur->pair.first, key)) {
        prev = leaf_cur;
        leaf_cur = (LeafNode *)(leaf_cur->next);
      }
    } else {
      while (cur != NULL && KeyCmpLessEqual(cur->key, key)) {
        prev = cur;
        cur = (InnerNode *)(cur->next);
      }
    }
    if (cur_level == level) return prev;
    cur_level--;
    if (prev == NULL) {
      cur = (InnerNode *)head_nodes[cur_level].next;
    } else {
      cur = (InnerNode *)(((InnerNode *)prev)->down);
      prev = NULL;
    }
  }
}

///////////////////////////////////////////////////////////////////
// Forward Iterator
///////////////////////////////////////////////////////////////////

SKIPLIST_TEMPLATE_ARGUMENTS
SKIPLIST_TYPE::ForwardIterator::ForwardIterator(SKIPLIST_TYPE *p_list_p)
    : list_p{p_list_p} {
  lf_node = (SKIPLIST_TYPE::LeafNode *)list_p->head_nodes[0].next;
}

SKIPLIST_TEMPLATE_ARGUMENTS
SKIPLIST_TYPE::ForwardIterator::ForwardIterator(SKIPLIST_TYPE *p_list_p,
                                                const KeyType &start_key)
    : list_p{p_list_p} {
  LowerBound(start_key);
}

SKIPLIST_TEMPLATE_ARGUMENTS
bool SKIPLIST_TYPE::ForwardIterator::IsEnd() const { return lf_node == NULL; }

SKIPLIST_TEMPLATE_ARGUMENTS
void SKIPLIST_TYPE::ForwardIterator::LowerBound(const KeyType &start_key_p) {
  lf_node = (SKIPLIST_TYPE::LeafNode *)list_p->Search(start_key_p, 0);
  if (lf_node && list_p->KeyCmpLess(lf_node->pair.first, start_key_p)) {
    lf_node = (SKIPLIST_TYPE::LeafNode *)lf_node->next;
  }
  PL_ASSERT(lf_node == nullptr ||
            KeyCmpLessEqual(start_key_p, lf_node->pair.first));
}

}  // namespace index
}  // namespace peloton
