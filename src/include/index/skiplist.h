//===----------------------------------------------------------------------===//
//
//                         Peloton
//
// skiplist.h
//
// Identification: src/include/index/skiplist.h
//
// Copyright (c) 2015-17, Carnegie Mellon University Database Group
//
//===----------------------------------------------------------------------===//

#pragma once
#include <vector>
#include <utility>
#include <functional>
#include <iostream>
namespace peloton {
namespace index {

/*
 * SKIPLIST_TEMPLATE_ARGUMENTS - Save some key strokes
 */
#define SKIPLIST_TEMPLATE_ARGUMENTS                                       \
  template <typename KeyType, typename ValueType, typename KeyComparator, \
            typename KeyEqualityChecker, typename ValueEqualityChecker>

#define SKIPLIST_TYPE                                             \
  SkipList<KeyType, ValueType, KeyComparator, KeyEqualityChecker, \
           ValueEqualityChecker>

#define MAX_NUM_LEVEL 32

template <typename KeyType, typename ValueType, typename KeyComparator,
          typename KeyEqualityChecker, typename ValueEqualityChecker>
class SkipList {
 public:
  using KeyValuePair = std::pair<KeyType, ValueType>;

  ///////////////////////////////////////////////////////////////////
  // Node Types
  ///////////////////////////////////////////////////////////////////
  class BaseNode {
   public:
    BaseNode *next;
  };

  class HeadNode : public BaseNode {};

  class InnerNode : public BaseNode {
   public:
    KeyType key;
    BaseNode *down;
    InnerNode *up;
  };

  class LeafNode : public BaseNode {
   public:
    KeyValuePair pair;
    InnerNode *up;
    bool deleted;
  };

  ///////////////////////////////////////////////////////////////////
  // Key Comparison Member Functions
  ///////////////////////////////////////////////////////////////////

  /*
   * KeyCmpLess() - Compare two keys for "less than" relation
   *
   * If key1 < key2 return true
   * If not return false
   */
  inline bool KeyCmpLess(const KeyType &key1, const KeyType &key2) const {
    return key_cmp_obj(key1, key2);
  }

  /*
   * KeyCmpGreater() - Compare a pair of keys for > relation
   *
   * It flips input for keyCmpLess()
   */
  inline bool KeyCmpGreater(const KeyType &key1, const KeyType &key2) const {
    return KeyCmpLess(key2, key1);
  }

  /*
   * KeyCmpLessEqual() - Compare a pair of keys for <= relation
   */
  inline bool KeyCmpLessEqual(const KeyType &key1, const KeyType &key2) const {
    return !KeyCmpGreater(key1, key2);
  }

  ////////////////////////////////////////////////////////////////////
  // Interface Method Implementation
  ////////////////////////////////////////////////////////////////////

  bool Insert(const KeyType &key, const ValueType &value) {
    // Check whether we should insert the new entry
    auto it = Begin(key);
    while (!it.IsEnd() && key_eq_obj(it->first, key)) {
      if (!duplicated_key) return false;
      if (value_eq_obj(it->second, value)) return false;
      ++it;
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
      for (int i = 1; i < levels - 1; i++) {
        in_nodes[i]->key = key;
        in_nodes[i]->down = in_nodes[i - 1];
        in_nodes[i]->up = in_nodes[i + 1];
      }
      // bottom innernode
      in_nodes[0]->key = key;
      in_nodes[0]->down = lf_node;
      in_nodes[0]->up = in_nodes[1];
      // top innernode
      in_nodes[levels - 1]->key = key;
      in_nodes[levels - 1]->down = in_nodes[levels - 2];
      in_nodes[levels - 1]->up = NULL;
    }

    // Find the position to insert the key for each level
    void *ptr;
  link_level_0:
    ptr = Search(key, 0);
    if (ptr == NULL) {
      lf_node->next = head_nodes[0].next;
      while (!__sync_bool_compare_and_swap(&head_nodes[0].next, lf_node->next,
                                           lf_node)) {
        goto link_level_0;
      }
    } else {
      lf_node->next = ((LeafNode *)ptr)->next;
      while (!__sync_bool_compare_and_swap(&(((LeafNode *)ptr)->next),
                                           lf_node->next, lf_node)) {
        goto link_level_0;
      }
    }

    for (int i = 1; i <= levels; i++) {
    link_level_i:
      void *ptr = Search(key, i);
      if (ptr == NULL) {
        in_nodes[i - 1]->next = head_nodes[i].next;
        while (!__sync_bool_compare_and_swap(&head_nodes[i].next,
                                             in_nodes[i - 1]->next,
                                             in_nodes[i - 1])) {
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

  //  bool Delete(const KeyType &key, const ValueType &value);

  void GetValue(const KeyType &search_key, std::vector<ValueType> &value_list) {
    auto it = Begin(search_key);

    while (!it.IsEnd() && key_eq_obj(it->first, search_key)) {
      value_list.push_back(it->second);
      ++it;
    }
  }
  //
  //  ///////////////////////////////////////////////////////////////////
  //  // Garbage Collection
  //  ///////////////////////////////////////////////////////////////////
  //  bool NeedGarbageCollection();
  //  void PerformGarbageCollection();
  //

  ///////////////////////////////////////////////////////////////////
  // Forward Iterator
  ///////////////////////////////////////////////////////////////////

  /*
   * class ForwardIterator - Iterator that supports forward iteration of list
   *                         elements
   */
  class ForwardIterator;

  /*
   * Begin() - Return an iterator pointing to the first element in the list, or
   * an
   *           end iterator if the list is empty.
   */
  ForwardIterator Begin() { return ForwardIterator{this}; }

  /*
   * Begin() - Return an iterator using a given key
   *
   * The iterator returned will point to the first data item whose key is
   * greater
   * than or equal to the given start key.
   */
  ForwardIterator Begin(const KeyType &start_key) {
    return ForwardIterator{this, start_key};
  }

  /*
   * class ForwardIterator - Iterator that supports forward iteration of list
   *                         elements
   */
  class ForwardIterator {
   private:
    LeafNode *lf_node;
    SKIPLIST_TYPE *list_p;

   public:
    /*
     * Constructor
     *
     * The iterator will point to the first element in the list, or an
     * end iterator if the list is empty.
     */
    ForwardIterator(SKIPLIST_TYPE *p_list_p) : list_p{p_list_p} {
      lf_node = (LeafNode *)list_p->head_nodes[0].next;
      MoveAheadToUndeletedNode();
    }

    /*
     * Constructor - Construct an iterator given a key
     *
     * The iterator will point to the first data item whose key is greater
     * than or equal to the given start key, or an end iterator if the list
     * is empty.
     */
    ForwardIterator(SKIPLIST_TYPE *p_list_p, const KeyType &start_key)
        : list_p{p_list_p} {
      LowerBound(start_key);
    }

    /*
     * IsEnd() - Whether the current iterator has reached the end of the list
     */
    bool IsEnd() const { return lf_node == NULL; }

    /*
     * LowerBound() - Load leaf page whose key >= start_key
     */
    void LowerBound(const KeyType &start_key_p) {
      lf_node = (LeafNode *)list_p->Search(start_key_p, 0);

      if (lf_node == nullptr) {
        // There is no node whose key <= start_key
        lf_node = (LeafNode *)list_p->head_nodes[0].next;
      } else if (list_p->KeyCmpLess(lf_node->pair.first, start_key_p)) {
        // There is no node whose key == start_key. Now lf_node is the last
        // one whose key < start_key.
        lf_node = (LeafNode *)lf_node->next;
      }
      MoveAheadToUndeletedNode();

      PL_ASSERT(lf_node == nullptr ||
                KeyCmpLessEqual(start_key_p, lf_node->pair.first));
    }

    /*
     * operator*() - Return the value reference currently pointed to by this
     *               iterator
     */
    inline const KeyValuePair &operator*() { return *lf_node->pair; }

    /*
     * operator->() - Returns the value pointer pointed to by this iterator
     */
    inline const KeyValuePair *operator->() { return &lf_node->pair; }

    /*
     * Prefix operator++ - Move the iterator ahead
     *
     * The caller is responsible for checking whether the iterator has reached
     * its end.
     */
    inline ForwardIterator &operator++() {
      MoveAheadByOne();
      return *this;
    }

    /*
     * MoveAheadByOne() - Move the iterator ahead by one
     *
     * The caller is responsible for checking whether the iterator has reached
     * its end. If iterator has reached end then assertion fails.
     */
    inline void MoveAheadByOne() {
      PL_ASSERT(lf_node != nullptr);
      lf_node = (LeafNode *)lf_node->next;
      MoveAheadToUndeletedNode();
    }

    /*
     * MoveAheadToUndeletedNode() - Move the iterator ahead to the first
     * undeleted node
     *
     * If the iterator is currently pointing to an undeleted node, then it
     * will not be moved. If there is no undeleted node after the iterator,
     * then it will become an end iterator.
     */
    inline void MoveAheadToUndeletedNode() {
      while (lf_node && lf_node->deleted) {
        lf_node = (LeafNode *)lf_node->next;
      }
    }
  };

  ///////////////////////////////////////////////////////////////////
  // Utility Funciton
  ///////////////////////////////////////////////////////////////////
  bool IsEmpty() { return head_nodes[0].next == NULL; }

  void PrintSkipList() {
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
      std::cout << "(" << cur->pair.first << ", " << cur->pair.second
                << ") --->";
      cur = static_cast<LeafNode *>(cur->next);
    }
    std::cout << std::endl;
  }

  /* It returns the pointer to the node with the largest key <= @key at
   * @level. If there are multiple nodes with keys == @key, then it
   * returns the first node.
   *
   * Ex: Search(5, 0) returns a pointer to the first 5
   *   [level 0]: -> 3 -> 4 -> 4 -> 5 -> 5 -> 6
   *
   * Ex: Search(5, 0) returns a pointer to the second 4
   *   [level 0]: -> 3 -> 4 -> 4 -> 6 -> 6 -> 6
   *
   *
   * IMPORTANT: It ignores delete flags. If this is not what you want,
   * you might consider using ForwardIterators.
   *
   *
   * It returns a pointer to InnerNode if @level > 0 and a pointer to
   * LeafNode if @level == 0.
   *
   * If the there is no node before the key at that level, it returns NULL.
   * (NOTE: It will not return a pointer to HeadNode.)
   *
   * Ex: Search(5, 0) returns NULL
   *   [level 0]: -> 6 -> 7 -> 8
   *
   * It returns NULL if @level is invalid, meaning @level is not in
   * [0, MAX_NUM_LEVEL-1].
   * */
  void *Search(const KeyType &key, int level) {
    // Check if skiplist is empty and valid parameter
    if (IsEmpty()) return NULL;
    if (level > max_level || level < 0) return NULL;

    void *ptr = SearchLower(key, level);
    if (ptr != NULL) {
      if (level == 0) {
        LeafNode *next = (LeafNode *)(((LeafNode *)ptr)->next);
        if (next != NULL && key_eq_obj(next->pair.first, key))
          return next;
        else
          return ptr;
      } else {
        InnerNode *next = (InnerNode *)(((InnerNode *)ptr)->next);
        if (next != NULL && key_eq_obj(next->key, key))
          return next;
        else
          return ptr;
      }
    } else {
      if (level == 0) {
        LeafNode *next = (LeafNode *)(head_nodes[level].next);
        if (next != NULL && key_eq_obj(next->pair.first, key))
          return next;
        else
          return ptr;
      } else {
        InnerNode *next = (InnerNode *)(head_nodes[level].next);
        if (next != NULL && key_eq_obj(next->key, key))
          return next;
        else
          return ptr;
      }
    }
  }

  /* It returns the pointer to the node with the largest key strictly < @key
   * at @level. If there are multiple largest nodes when duplicated keys are
   * allowed, it returns the last one.
   *
   * Ex: SearchLower(5, 0) returns a pointer to the second 4
   *   3-> 4 -> 4 -> 5 -> 5 -> 6
   *
   * IMPORTANT: It ignores delete flags. If this is not what you want,
   * you might consider using ForwardIterators.
   *
   * It returns a pointer to InnerNode if @level > 0 and a pointer to
   * LeafNode if @level == 0.
   *
   * If the there is no node before the key at that level, it returns NULL.
   * (NOTE: It will not return a pointer to HeadNode.)
   *
   * Ex: SearchLower(5, 0) returns NULL
   *   [level 0]: -> 6 -> 7 -> 8
   *
   * It returns NULL if @level is invalid, meaning @level is not in
   * [0, MAX_NUM_LEVEL-1].
   * */
  void *SearchLower(const KeyType &key, int level) {
    // Check if skiplist is empty
    if (IsEmpty()) return NULL;
    if (level > max_level || level < 0) return NULL;

    int cur_level = max_level;
    InnerNode *cur = (InnerNode *)head_nodes[cur_level].next;
    void *prev = NULL;
    while (1) {
      if (cur_level == 0) {
        LeafNode *leaf_cur = (LeafNode *)cur;
        while (leaf_cur != NULL && KeyCmpLess(leaf_cur->pair.first, key)) {
          prev = leaf_cur;
          leaf_cur = (LeafNode *)(leaf_cur->next);
        }
      } else {
        while (cur != NULL && KeyCmpLess(cur->key, key)) {
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

 public:
  // Constructor
  SkipList(bool p_duplicated_key = false,
           KeyComparator p_key_cmp_obj = KeyComparator{},
           KeyEqualityChecker p_key_eq_obj = KeyEqualityChecker{},
           ValueEqualityChecker p_value_eq_obj = ValueEqualityChecker{})
      : duplicated_key(p_duplicated_key),
        key_cmp_obj(p_key_cmp_obj),
        key_eq_obj(p_key_eq_obj),
        value_eq_obj(p_value_eq_obj) {
    for (int i = 0; i < MAX_NUM_LEVEL; i++) head_nodes[i] = HeadNode();
  };

  // Destructor
  ~SkipList() {
    for (unsigned i = 1; i < MAX_NUM_LEVEL; i++) {
      InnerNode *cur = (InnerNode *)head_nodes[i].next;
      InnerNode *prev = NULL;
      while (cur != NULL) {
        prev = cur;
        cur = (InnerNode *)(cur->next);
        delete prev;
      }
    }
    LeafNode *cur = (LeafNode *)head_nodes[0].next;
    LeafNode *prev = NULL;
    while (cur != NULL) {
      prev = cur;
      cur = (LeafNode *)(cur->next);
      delete prev;
    }
  }

 public:
  const bool duplicated_key;
  // Key comparator
  const KeyComparator key_cmp_obj;

  // Raw key eq checker
  const KeyEqualityChecker key_eq_obj;

  const ValueEqualityChecker value_eq_obj;

  HeadNode head_nodes[MAX_NUM_LEVEL];

  // max_level falls in [0, MAX_NUM_LEVEL]
  int max_level = 0;

 private:
  // Used for finding the least significant bit
  const int MultiplyDeBruijnBitPosition[32] = {
      0,  1,  28, 2,  29, 14, 24, 3, 30, 22, 20, 15, 25, 17, 4,  8,
      31, 27, 13, 23, 21, 19, 16, 7, 26, 12, 18, 6,  11, 5,  10, 9};
};

}  // namespace index
}  // namespace peloton
