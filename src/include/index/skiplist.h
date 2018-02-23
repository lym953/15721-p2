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
  //  ///////////////////////////////////////////////////////////////////
  //  // Forward Iterator
  //  ///////////////////////////////////////////////////////////////////
  //  /*
  //   * Iterator Interface
  //   */
  //  class ForwardIterator;
  //  ForwardIterator Begin();
  //  ForwardIterator Begin(const KeyType &start_key);
  //  bool IsEnd() const;
  //  inline ForwardIterator &operator++();
  //    ///////////////////////////////////////////////////////////////////
  //    // Utility Funciton
  //    ///////////////////////////////////////////////////////////////////
  bool IsEmpty() { return head_nodes[0].next == NULL; }
  void PrintSkipList();

 public:
  // Constructor
  SkipList(KeyComparator p_key_cmp_obj = KeyComparator{},
           KeyEqualityChecker p_key_eq_obj = KeyEqualityChecker{},
           ValueEqualityChecker p_value_eq_obj = ValueEqualityChecker{})
      : key_cmp_obj(p_key_cmp_obj),
        key_eq_obj(p_key_eq_obj),
        value_eq_obj(p_value_eq_obj) {
    head_nodes.push_back(HeadNode());
  };

  // Destructor
  ~SkipList() {
    for (unsigned i = 1; i < head_nodes.size(); i++) {
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
  // Key comparator
  const KeyComparator key_cmp_obj;

  // Raw key eq checker
  const KeyEqualityChecker key_eq_obj;

  const ValueEqualityChecker value_eq_obj;

  std::vector<HeadNode> head_nodes;

 private:
  void *Search(const KeyType &key, int level);
};

}  // namespace index
}  // namespace peloton
