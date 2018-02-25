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

  class LeafNode : public BaseNode {
   public:
    KeyValuePair pair;
  };

  class InnerNode : public BaseNode {
   public:
    KeyType key;
    BaseNode *down;
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
  bool Insert(const KeyType &key, const ValueType &value);
  //  bool ConditionalInsert(const KeyType &key, const ValueType &value,
  //                         std::function<bool(const void *)> predicate,
  //                         bool *predicate_satisfied);
  //  bool Delete(const KeyType &key, const ValueType &value);
  //  void GetValue(const KeyType &search_key, std::vector<ValueType>
  //  &value_list);
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
    ForwardIterator(SKIPLIST_TYPE *p_list_p);

    /*
     * Constructor - Construct an iterator given a key
     *
     * The iterator will point to the first data item whose key is greater
     * than or equal to the given start key, or an end iterator if the list
     * is empty.
     */
    ForwardIterator(SKIPLIST_TYPE *p_list_p, const KeyType &start_key);

    /*
     * IsEnd() - Whether the current iterator has reached the end of the list
     */
    bool IsEnd() const;

    /*
     * LowerBound() - Load leaf page whose key >= start_key
     */
    void LowerBound(const KeyType &start_key_p);

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
      lf_node = (SKIPLIST_TYPE::LeafNode *)lf_node->next;
    }
  };

  //    ///////////////////////////////////////////////////////////////////
  //    // Utility Funciton
  //    ///////////////////////////////////////////////////////////////////
  bool IsEmpty() { return head_nodes[0].next == NULL; }
  void PrintSkipList();

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

  // max_level falls in [0, 31]
  int max_level;

 private:
  void *Search(const KeyType &key, int level);
};

}  // namespace index
}  // namespace peloton
