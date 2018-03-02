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
#include <map>
#include <set>
#include <atomic>
#include <thread>

#include "common/logger.h"
#include "common/macros.h"
#include "util/string_util.h"
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

// This is the value we use in epoch manager to make sure
// no thread sneaking in while GC decision is being made
#define MAX_THREAD_COUNT ((int)0x7FFFFFFF)

template <typename KeyType, typename ValueType, typename KeyComparator,
          typename KeyEqualityChecker, typename ValueEqualityChecker>
class SkipList {
  // Public Classes Declarations
 public:
  class EpochManager;
  class BaseNode;
  class HeadNode;
  class InnerNode;
  class LeafNode;
  class ValueNode;
  class ForwardIterator;

 public:
  using KeyValuePair = std::pair<KeyType, ValueType>;

  using EpochNode = typename EpochManager::EpochNode;

  ///////////////////////////////////////////////////////////////////
  // Node Types
  ///////////////////////////////////////////////////////////////////
  enum class NodeType : short {
    BaseNode = 0,

    HeadNode = 1,
    InnerNode = 2,
    LeafNode = 3,
    ValueNode = 4,
  };

  class BaseNode {
   public:
    BaseNode *next = NULL;
    NodeType type = NodeType::BaseNode;

   public:
    NodeType GetNodeType() { return type; }
  };

  class HeadNode : public BaseNode {
   public:
    HeadNode() { BaseNode::type = NodeType::HeadNode; }
  };

  class InnerNode : public BaseNode {
   public:
    KeyType key;
    BaseNode *down;

   public:
    InnerNode(const KeyType &key) : key(key), down(NULL) {
      BaseNode::type = NodeType::InnerNode;
    }
  };

  class ValueNode : public BaseNode {
   public:
    ValueType value;

   public:
    ValueNode(const ValueType &value) : value(value) {
      BaseNode::type = NodeType::ValueNode;
    }
  };

  class LeafNode : public BaseNode {
   public:
    KeyType key;
    ValueNode *head;

   public:
    LeafNode(const KeyType &key) : key(key), head(NULL) {
      BaseNode::type = NodeType::LeafNode;
    }
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

  /**
   * KeyCmpEqual() - Compare two key pair for == relation
   */
  inline bool KeyCmpEqual(const KeyType &key1, const KeyType &key2) const {
    return key_eq_obj(key1, key2);
  }

  /*
   * KeyCmpLessEqual() - Compare two key-value pair for == relation
   */
  inline bool KeyValueCmpEqual(const KeyValuePair &kvp1,
                               const KeyValuePair &kvp2) const {
    return (key_eq_obj(kvp1.first, kvp2.first) &&
            value_eq_obj(kvp1.second, kvp2.second));
  }

  /**
   * ValueCmpEqual() - Compare two values for == relation
   */
  inline bool ValueCmpEqual(const ValueType &val1,
                            const ValueType &val2) const {
    return value_eq_obj(val1, val2);
  }

  ////////////////////////////////////////////////////////////////////
  // Interface Method Implementation
  ////////////////////////////////////////////////////////////////////

  BaseNode *SearchPlaceToInsertLeaf(const KeyType &key, bool &valid) {
    LeafNode *ptr = (LeafNode *)SearchLower(key, 0);
    if (ptr == NULL) {
      if (head_nodes[0].next == NULL) {
        valid = true;
        return &head_nodes[0];
      }
      BaseNode *prev = &head_nodes[0];
      ptr = (LeafNode *)(head_nodes[0].next);
      while (ptr != NULL && !KeyCmpGreater(ptr->key, key)) {
        bool same_key = key_eq_obj(ptr->key, key);
        bool deleted = ptr->head->next == NULL;
        if (same_key && !deleted) {
          valid = false;
          return ptr;
        }
        prev = ptr;
        ptr = (LeafNode *)(ptr->next);
      }
      valid = true;
      return prev;
    } else {
      LeafNode *prev = ptr;
      while (ptr != NULL && !KeyCmpGreater(ptr->key, key)) {
        bool same_key = key_eq_obj(ptr->key, key);
        bool deleted = ptr->head->next == NULL;
        if (same_key && !deleted) {
          valid = false;
          return ptr;
        }
        prev = ptr;
        ptr = (LeafNode *)(ptr->next);
      }
      valid = true;
      return prev;
    }
  }

  bool Insert(const KeyType &key, const ValueType &value) {
    EpochNode *epoch_node_p = epoch_manager.JoinEpoch();

    // Create LeafNode and ValueNode and append
    LeafNode *lf_node = new LeafNode(key);
    ValueNode *dummy = new ValueNode(value);  // this value is useless
    ValueNode *v_node = new ValueNode(value);
    lf_node->head = dummy;
    dummy->next = v_node;

    size_t memory_claimed =
        size_of_leaf_node + size_of_inner_node + size_of_value_node;

  // Update memory used
  update_memory:
    size_t cur_memory_used = memory_used;
    while (!__sync_bool_compare_and_swap(&memory_used, cur_memory_used,
                                         cur_memory_used + memory_claimed)) {
      goto update_memory;
    }

  // Find the place to insert LeafNode
  search_place_to_insert:
    bool is_valid;
    BaseNode *leaf_start_insert = SearchPlaceToInsertLeaf(key, is_valid);
    if (is_valid) {
      lf_node->next = leaf_start_insert->next;
      if (lf_node->next &&
          !KeyCmpGreater(((LeafNode *)(lf_node->next))->key, key)) {
        goto search_place_to_insert;
      }
      while (!__sync_bool_compare_and_swap(&leaf_start_insert->next,
                                           lf_node->next, lf_node)) {
        goto search_place_to_insert;
      }

      // Add Tower
      // Determine the height of the tower
      int v = rand();
      int levels =
          MultiplyDeBruijnBitPosition[((uint32_t)((v & -v) * 0x077CB531U)) >>
                                      27];
      InnerNode *in_nodes[levels];
      if (levels > 0) {
        for (int i = 0; i < levels; i++) in_nodes[i] = new InnerNode(key);
        if (levels > 1) {
          // Link InnerNodes
          for (int i = 1; i < levels - 1; i++) {
            in_nodes[i]->down = in_nodes[i - 1];
          }
          // bottom innernode
          in_nodes[0]->down = lf_node;
          // top innernode
          in_nodes[levels - 1]->down = in_nodes[levels - 2];
        } else {
          in_nodes[0]->down = lf_node;
        }
      }
      // Find the position to insert InnerNode for each level
      for (int i = 1; i <= levels; i++) {
      link_level_i:
        void *ptr = SearchLower(key, i);
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
        while (
            !__sync_bool_compare_and_swap(&max_level, cur_max_level, levels)) {
          goto update_max_level;
        }
      }
      epoch_manager.LeaveEpoch(epoch_node_p);
      return true;
    } else {
      // someone has insert this leafNode
      if (!duplicated_key) {
        epoch_manager.AddGarbageNode(lf_node);
        epoch_manager.AddGarbageNode(v_node);
        epoch_manager.LeaveEpoch(epoch_node_p);
        return false;
      }

      // we allow duplicated key
      v_node->next = ((LeafNode *)leaf_start_insert)->head->next;
      if (v_node->next == NULL) goto search_place_to_insert;
      // check if already contains the same value
      ValueNode *ptr = (ValueNode *)(v_node->next);
      bool same = false;
      while (ptr != NULL) {
        if (value_eq_obj(ptr->value, value)) {
          same = true;
          break;
        }
        ptr = (ValueNode *)(ptr->next);
      }
      if (same) {
        epoch_manager.AddGarbageNode(lf_node);
        epoch_manager.AddGarbageNode(v_node);
        epoch_manager.LeaveEpoch(epoch_node_p);
        return false;
      } else {
        // update head so that it points to you
        while (!__sync_bool_compare_and_swap(
                   &(((LeafNode *)leaf_start_insert)->head->next),
                   (ValueNode *)(v_node->next), v_node)) {
          goto search_place_to_insert;
        }
        epoch_manager.AddGarbageNode(lf_node);
        epoch_manager.LeaveEpoch(epoch_node_p);
        return true;
      }
    }
    return true;
  }

  /**
   * Implement delete operation.
   * perform logical deletion - mark the base node as deleted.
   * The physical deletion will be performed by garbage collection.
   * The DeleteEntry function should erase only the index entry matching the
   * specific <key, value> pair.
   */
  bool Delete(const KeyType &key, const ValueType &value) {
    EpochNode *epoch_node_p = epoch_manager.JoinEpoch();
    // Check if skiplist is empty
    if (IsEmpty()) {
      epoch_manager.LeaveEpoch(epoch_node_p);
      return false;
    }

    // find the first level containing this key.
    void *start_node = NULL;
    int start_level = -1;
    for (int i = max_level; i >= 0; i--) {
      // search all the levels until I got my node.
      start_node = Search(key, i);
      if (start_node != NULL) {
        if (i != 0) {
          if (KeyCmpEqual(((InnerNode *)start_node)->key, key)) {
            start_level = i;
            break;
          }
        } else {
          if (KeyCmpEqual(((LeafNode *)start_node)->key, key)) {
            start_level = i;
            break;
          }
        }
      }
    }
    // If I can't find a tower for this key. already deleted.
    if (start_level == -1) {
      epoch_manager.LeaveEpoch(epoch_node_p);
      return false;
    }

    // find the leafNode to delete - this must exist because of the down
    // pointer.
    LeafNode *leafNode = (LeafNode *)FindLeafNode(start_node, start_level);
    if (leafNode == NULL) {
      epoch_manager.LeaveEpoch(epoch_node_p);
      return false;
    }
    // find the node to be deleted
    ValueNode *node_to_delete = SearchValueNode(leafNode, value, false);
    if (node_to_delete == NULL) {
      epoch_manager.LeaveEpoch(epoch_node_p);
      return false;
    }

    ValueNode *findPrev = NULL;
  // delete this
  delete_value_node:
    // start to cmp swap this.
    findPrev = SearchValueNode(leafNode, value, true);
    // this value already has been deleted by another thread.
    if (findPrev == NULL) {
      epoch_manager.LeaveEpoch(epoch_node_p);
      return false;
    }
    // cas this value node.
    while (!__sync_bool_compare_and_swap(&(findPrev->next),
                                         ((BaseNode *)node_to_delete),
                                         node_to_delete->next)) {
      goto delete_value_node;
    }

    epoch_manager.AddGarbageNode(node_to_delete);

    // check whether we need to delete the whole branch.
    bool delete_branch = false;
    if (findPrev == leafNode->head && node_to_delete->next == NULL) {
      delete_branch = true;
    }
    // start to delete this node. search from top to bottom.
    // prev may be a normal inner node, or a head node.
    // but no matter of what, it should give you prev.
    if (delete_branch) {
      for (int i = start_level; i >= 1; i--) {
      link_level_i:
        // find the node pointing to the current node.
        // no thread can delete the same branch at the same time.
        void *ptr = SearchNode(start_node, i);
        // possibily header node.
        if (ptr == NULL) {
          epoch_manager.LeaveEpoch(epoch_node_p);
          return false;
        } else {
          if (ptr == &head_nodes[i] && ((BaseNode *)start_node)->next == NULL) {
            int cur_max_level = max_level;
            if (cur_max_level == i) {
              // do we care if this set fails?
              __sync_bool_compare_and_swap(&max_level, cur_max_level,
                                           cur_max_level - 1);
            }
          }
          // set ptr's next to my current's next.
          while (!__sync_bool_compare_and_swap(
                     &(((InnerNode *)(ptr))->next), (BaseNode *)start_node,
                     ((BaseNode *)start_node)->next)) {
            goto link_level_i;
          }
        }
        // move to next level.
        BaseNode *temp = (BaseNode *)start_node;

        start_node = (void *)((InnerNode *)start_node)->down;

        epoch_manager.AddGarbageNode(temp);
      }

    // cas the bottom one.
    link_level_0:
      void *ptr = SearchNode(start_node, 0);
      if (ptr != NULL) {
        // we don't reduce max level here because it's already 0.
        while (!__sync_bool_compare_and_swap(&(((LeafNode *)ptr)->next),
                                             (BaseNode *)start_node,
                                             ((BaseNode *)start_node)->next)) {
          goto link_level_0;
        }
      } else {
        epoch_manager.LeaveEpoch(epoch_node_p);
        return false;
      }

      epoch_manager.AddGarbageNode((BaseNode *)start_node);
    }

    epoch_manager.LeaveEpoch(epoch_node_p);
    return true;
  }

  void GetValue(const KeyType &search_key, std::vector<ValueType> &value_list) {
    auto it = Begin(search_key);

    while (!it.IsEnd() && key_eq_obj(it.GetKey(), search_key)) {
      value_list.push_back(it.GetValue());
      ++it;
    }
  }

  ///////////////////////////////////////////////////////////////////
  // Garbage Collection
  ///////////////////////////////////////////////////////////////////
  bool NeedGarbageCollection() { return true; };

  void PerformGarbageCollection() { epoch_manager.PerformGarbageCollection(); };

  ///////////////////////////////////////////////////////////////////
  // Forward Iterator
  ///////////////////////////////////////////////////////////////////

  /*
   * Begin() - Return an iterator pointing to the first element in the list, or
   * an end iterator if the list is empty.
   */
  ForwardIterator Begin() { return ForwardIterator{this}; }

  /*
   * Begin() - Return an iterator using a given key
   *
   * The iterator returned will point to the first data item whose key is
   * greater than or equal to the given start key.
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
    ValueNode *val_node;
    SKIPLIST_TYPE *list_p;

   public:
    /*
     * Constructor
     *
     * The iterator will point to the first element in the list, or become an
     * end iterator if the list is empty.
     */
    ForwardIterator(SKIPLIST_TYPE *p_list_p) : list_p{p_list_p} {
      lf_node = (LeafNode *)list_p->head_nodes[0].next;
      val_node = (ValueNode *)lf_node->head->next;
      MoveAheadToUndeletedNode();
    }

    /*
     * Constructor - Construct an iterator given a key
     *
     * The iterator will point to the first data item whose key is greater
     * than or equal to the given start key, or become an end iterator if the
     * list is empty.
     */
    ForwardIterator(SKIPLIST_TYPE *p_list_p, const KeyType &start_key)
        : list_p{p_list_p} {
      LowerBound(start_key);
    }

    /*
     * IsEnd() - Whether the current iterator has reached the end of the list
     */
    bool IsEnd() const { return lf_node == nullptr; }

    /*
     * LowerBound() - Find entry whose key >= start_key
     */
    void LowerBound(const KeyType &start_key_p) {
      lf_node = (LeafNode *)(list_p->Search(start_key_p, 0));

      if (lf_node == nullptr) {
        // There is no node whose key <= start_key
        lf_node = (LeafNode *)(list_p->head_nodes[0].next);
      } else if (list_p->KeyCmpLess(lf_node->key, start_key_p)) {
        // There is no node whose key == start_key. Now lf_node is the last
        // one whose key < start_key.
        lf_node = (LeafNode *)(lf_node->next);
      }
      if (lf_node != NULL) {
        val_node = (ValueNode *)(lf_node->head->next);
        MoveAheadToUndeletedNode();
      }
      //
      //      PL_ASSERT(lf_node == nullptr ||
      //                KeyCmpLessEqual(start_key_p, lf_node->key));
    }

    /*
     * GetKey() - Get the key pointed by the iterator
     *
     * The caller is responsible for checking whether the iterator has reached
     * its end. If yes then assertion will fail.
     */
    inline const KeyType GetKey() {
      PL_ASSERT(lf_node);
      return lf_node->key;
    }

    /*
     * GetValue() - Get the value pointed by the iterator
     *
     * The caller is responsible for checking whether the iterator has reached
     * its end. If yes then assertion will fail.
     */
    inline const ValueType GetValue() {
      PL_ASSERT(val_node);
      return val_node->value;
    }

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
      PL_ASSERT(val_node != nullptr);
      val_node = (ValueNode *)val_node->next;
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
      // reach the end of the list
      if (lf_node == nullptr) return;

      while (val_node == nullptr) {
        // val_node == nullptr means we have reached the end of
        // ValueNode list for the current key. Go on to the next key.

        lf_node = (LeafNode *)lf_node->next;

        // reach the end of skiplist
        if (lf_node == nullptr) return;

        val_node = (ValueNode *)lf_node->head->next;
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
      std::cout << "(" << cur->key << ", [";
      // print value chain
      ValueNode *ptr = (ValueNode *)(cur->head->next);
      while (ptr != NULL) {
        std::cout << ptr->value << ", ";
        ptr = (ValueNode *)(ptr->next);
      }
      std::cout << "]) ---> ";
      cur = static_cast<LeafNode *>(cur->next);
    }
    std::cout << std::endl;
  }

  bool StructuralIntegrityCheck() {
    // Check if max_level is valid
    std::cout << "Checking max_level ... " << std::flush;
    if (max_level < 0 || max_level >= MAX_NUM_LEVEL) {
      std::cout << "Failed" << std::endl;
      return false;
    }
    std::cout << "Correct" << std::endl;

    // Check if it's sorted at each level (strictly increasings)
    std::cout << "Checking if it's strictly sorted at each level ... "
              << std::flush;
    for (int i = 1; i < MAX_NUM_LEVEL; i++) {
      InnerNode *ptr = (InnerNode *)(head_nodes[i].next);
      KeyType prev_key;
      if (ptr != NULL) {
        prev_key = ptr->key;
        ptr = (InnerNode *)(ptr->next);
      }
      while (ptr) {
        if (!KeyCmpLess(prev_key, ptr->key)) {
          std::cout << "Failed" << std::endl;
          return false;
        }
        prev_key = ptr->key;
        ptr = (InnerNode *)(ptr->next);
      }
    }
    LeafNode *ptr = (LeafNode *)(head_nodes[0].next);
    KeyType prev_key;
    if (ptr != NULL) {
      prev_key = ptr->key;
      ptr = (LeafNode *)(ptr->next);
    }
    while (ptr) {
      if (!KeyCmpLess(prev_key, ptr->key)) {
        std::cout << "Failed" << std::endl;
        return false;
      }
      prev_key = ptr->key;
      ptr = (LeafNode *)(ptr->next);
    }
    std::cout << "Correct" << std::endl;

    // Check if each InnerNode can reach a LeafNode that has the same key value
    std::cout << "Checking if InnerNode can reach a LeafNode that has the same "
                 "key value ... " << std::flush;
    for (int i = 1; i < MAX_NUM_LEVEL; i++) {
      InnerNode *cur = (InnerNode *)(head_nodes[i].next);
      while (cur != NULL) {
        InnerNode *ptr = cur;
        for (int j = i; j != 0; j--) {
          ptr = (InnerNode *)(ptr->down);
          if (ptr == NULL) {
            std::cout << "Failed (InnerNode cannot reach a LeafNode)"
                      << std::endl;
            return false;
          }
        }
        if (!key_eq_obj(((LeafNode *)ptr)->key, cur->key)) {
          std::cout << "Failed  (LeafNode has difference key than InnerNode)"
                    << std::endl;
          return false;
        }
        cur = (InnerNode *)cur->next;
      }
    }
    std::cout << "Correct" << std::endl;

    // TODO: Check if there's duplicated keys when duplicates are not allowed

    // TODO: Check if there's duplicated (key, value) pair when duplicates are
    // allowed
    return true;
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
        if (next != NULL && key_eq_obj(next->key, key))
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
        if (next != NULL && key_eq_obj(next->key, key))
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
        while (leaf_cur != NULL && KeyCmpLess(leaf_cur->key, key)) {
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

  /*****
   * We want to find a node in a certain level.
   * The method returns the previous node pointing to this node.
   **/
  void *SearchNode(const void *node, const int level) {
    void *prev = NULL;
    KeyType key;
    if (level == 0) {
      key = ((LeafNode *)node)->key;
    } else {
      key = ((InnerNode *)node)->key;
    }
    // find the node with key < key at level.
    prev = SearchLower(key, level);
    // we still want to search from start to avoid false positive.
    void *curr_node;
    if (prev == NULL) {
      prev = &head_nodes[level];
      curr_node = head_nodes[level].next;
    } else {
      curr_node = ((BaseNode *)prev)->next;
    }

    // start to find the node.
    while (curr_node != NULL) {
      // if the current node's key already greater than the key we want.
      // can't find the node.
      if (level == 0) {
        if (KeyCmpGreater(((LeafNode *)curr_node)->key, key)) {
          prev = NULL;
          break;
        }
      } else {
        if (KeyCmpGreater(((InnerNode *)curr_node)->key, key)) {
          prev = NULL;
          break;
        }
      }
      if (curr_node == node) {
        return prev;
      }
      // move to next one.
      prev = curr_node;
      curr_node = ((BaseNode *)curr_node)->next;
    }
    return NULL;
  }

  /***
   * This function wants to find the ValueNode to Delete.
   * return NULL.
   * if prev_node is true, then it means that it wants to find the
   * previous node pointing to the value node.
   */
  ValueNode *SearchValueNode(const LeafNode *leafNode, const ValueType &value,
                             bool prev_node) {
    ValueNode *prev = leafNode->head;
    ValueNode *curr = (ValueNode *)(prev->next);
    while (curr != NULL) {
      // if we found the valueNode.
      if (ValueCmpEqual(curr->value, value)) {
        if (prev_node) {
          return prev;
        } else {
          return curr;
        }
      }
      // move to next one.
      prev = curr;
      curr = (ValueNode *)curr->next;
    }
    return NULL;
  }

  /***
   * Find the leaf node given the start node
   */
  void *FindLeafNode(void *start_node, int level) {
    void *leaf_node = start_node;
    for (int i = level; i >= 1; i--) {
      leaf_node = ((InnerNode *)leaf_node)->down;
    }
    return leaf_node;
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
        value_eq_obj(p_value_eq_obj),

        epoch_manager(this) {
    LOG_TRACE(
        "SkipList Constructor called. "
        "Setting up execution environment...");

    size_of_inner_node = (sizeof(InnerNode));
    size_of_leaf_node = (sizeof(LeafNode));
    size_of_value_node = (sizeof(ValueNode));
    LOG_TRACE("size of nodes: Inner %d, Leaf %d, Value %d", size_of_inner_node,
              size_of_leaf_node, size_of_value_node);

    for (int i = 0; i < MAX_NUM_LEVEL; i++) head_nodes[i] = HeadNode();

    LOG_TRACE("Starting epoch manager thread...");
    epoch_manager.StartThread();
  };

  // Destructor
  ~SkipList() {
    // Free alive nodes
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
      // free value chain
      ValueNode *val_cur = prev->head;
      ValueNode *val_prev = NULL;
      while (val_cur != NULL) {
        val_prev = val_cur;
        val_cur = (ValueNode *)(val_cur->next);
        delete val_prev;
      }
      delete prev;
    }

    // TODO: Free dead nodes, i.e., nodes are in the memory pool.
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

  // tmp memory pool to recyle nodes.
  std::vector<void *> memory_pool;

  EpochManager epoch_manager;

  size_t size_of_inner_node;

  size_t size_of_leaf_node;

  size_t size_of_value_node;

  size_t memory_used = 0;

 public:
  /*
   * class EpochManager - Maintains a linked list of deleted nodes
   *                      for threads to access until all threads
   *                      entering epochs before the deletion of
   *                      nodes have exited
   */
  class EpochManager {
   public:
    SkipList *skiplist_p;

    // Garbage collection interval (milliseconds)
    constexpr static int GC_INTERVAL = 50;

    /*
     * struct GarbageNode - A linked list of garbages
     */
    struct GarbageNode {
      BaseNode *node_p;

      // This does not have to be atomic, since we only
      // insert at the head of garbage list
      GarbageNode *next_p;
    };

    /*
     * struct EpochNode - A linked list of epoch node that records thread count
     *
     * This struct is also the head of garbage node linked list, which must
     * be made atomic since different worker threads will contend to insert
     * garbage into the head of the list
     */
    struct EpochNode {
      // We need this to be atomic in order to accurately
      // count the number of threads
      std::atomic<int> active_thread_count;

      // We need this to be atomic to be able to
      // add garbage nodes without any race condition
      // i.e. GC nodes are CASed onto this pointer
      std::atomic<GarbageNode *> garbage_list_p;

      // This does not need to be atomic since it is
      // only maintained by the epoch thread
      EpochNode *next_p;
    };

    // The head pointer does not need to be atomic
    // since it is only accessed by epoch manager
    EpochNode *head_epoch_p;

    // This does not need to be atomic because it is only written
    // by the epoch manager and read by worker threads. But it is
    // acceptable that allocations are delayed to the next epoch
    EpochNode *current_epoch_p;

    // This flag indicates whether the destructor is running
    // If it is true then GC thread should not clean
    // Therefore, strict ordering is required
    std::atomic<bool> exited_flag;

    // If GC is done with external thread then this should be set
    // to nullptr
    // Otherwise it points to a thread created by EpochManager internally
    std::thread *thread_p;

    /*
     * Constructor - Initialize the epoch list to be a single node
     *
     * NOTE: We do not start thread here since the init of bw-tree itself
     * might take a long time
     */
    EpochManager(SkipList *p_skiplist_p) : skiplist_p{p_skiplist_p} {
      current_epoch_p = new EpochNode{};

      // These two are atomic variables but we could
      // simply assign to them
      current_epoch_p->active_thread_count = 0;
      current_epoch_p->garbage_list_p = nullptr;

      current_epoch_p->next_p = nullptr;

      head_epoch_p = current_epoch_p;

      // We allocate and run this later
      thread_p = nullptr;

      // This is used to notify the cleaner thread that it has ended
      exited_flag.store(false);

      return;
    }

    /*
     * Destructor - Stop the worker thread and cleanup resources not freed
     *
     * This function waits for the worker thread using join() method. After the
     * worker thread has exited, it synchronously clears all epochs that have
     * not been recycled by calling ClearEpoch()
     *
     * NOTE: If no internal GC is started then thread_p would be a nullptr
     * and we neither wait nor free the pointer.
     */
    ~EpochManager() {
      // Set stop flag and let thread terminate
      // Also if there is an external GC thread then it should
      // check this flag everytime it does cleaning since otherwise
      // the un-thread-safe function ClearEpoch() would be ran
      // by more than 1 threads
      exited_flag.store(true);

      // If thread pointer is nullptr then we know the GC thread
      // is not started. In this case do not wait for the thread, and just
      // call destructor
      //
      // NOTE: The destructor routine is not thread-safe, so if an external
      // GC thread is being used then that thread should check for
      // exited_flag everytime it wants to do GC
      //
      // If the external thread calls ThreadFunc() then it is safe
      if (thread_p != nullptr) {
        LOG_TRACE("Waiting for thread");

        thread_p->join();

        // Free memory
        delete thread_p;

        LOG_TRACE("Thread stops");
      }

      // So that in the following function the comparison
      // would always fail, until we have cleaned all epoch nodes
      current_epoch_p = nullptr;

      // If all threads has exited then all thread counts are
      // 0, and therefore this should proceed way to the end
      ClearEpoch();

      // If we have a bug (currently there is one) then as a temporary
      // measure just force cleaning all epoches no matter whether they
      // are cleared or not
      if (head_epoch_p != nullptr) {
        LOG_DEBUG("ERROR: After cleanup there is still epoch left");
        LOG_DEBUG("%s", peloton::GETINFO_THICK_LINE.c_str());
        LOG_DEBUG("DUMP");

        for (EpochNode *epoch_node_p = head_epoch_p; epoch_node_p != nullptr;
             epoch_node_p = epoch_node_p->next_p) {
          LOG_DEBUG("Active thread count: %d",
                    epoch_node_p->active_thread_count.load());
          epoch_node_p->active_thread_count = 0;
        }

        LOG_DEBUG("RETRY CLEANING...");
        ClearEpoch();
      }

      PL_ASSERT(head_epoch_p == nullptr);
      LOG_TRACE("Garbage Collector has finished freeing all garbage nodes");

      return;
    }

    /*
     * CreateNewEpoch() - Create a new epoch node
     *
     * This functions does not have to consider race conditions
     */
    void CreateNewEpoch() {
      LOG_TRACE("Creating new epoch...");

      EpochNode *epoch_node_p = new EpochNode{};

      epoch_node_p->active_thread_count = 0;
      epoch_node_p->garbage_list_p = nullptr;

      // We always append to the tail of the linked list
      // so this field for new node is always nullptr
      epoch_node_p->next_p = nullptr;

      // Update its previous node (current tail)
      current_epoch_p->next_p = epoch_node_p;

      // And then switch current epoch pointer
      current_epoch_p = epoch_node_p;

      return;
    }

    /*
     * AddGarbageNode() - Add garbage node into the current epoch
     *
     * NOTE: This function is called by worker threads so it has
     * to consider race conditions
     */
    void AddGarbageNode(BaseNode *node_p) {
      // We need to keep a copy of current epoch node
      // in case that this pointer is increased during
      // the execution of this function
      //
      // NOTE: Current epoch must not be recycled, since
      // the current thread calling this function must
      // come from an epoch <= current epoch
      // in which case all epochs before that one should
      // remain valid
      EpochNode *epoch_p = current_epoch_p;

      // These two could be predetermined
      GarbageNode *garbage_node_p = new GarbageNode;
      garbage_node_p->node_p = node_p;

      garbage_node_p->next_p = epoch_p->garbage_list_p.load();

      while (1) {
        // Then CAS previous node with new garbage node
        // If this fails, then garbage_node_p->next_p is the actual value
        // of garbage_list_p, in which case we do not need to load it again
        bool ret = epoch_p->garbage_list_p.compare_exchange_strong(
            garbage_node_p->next_p, garbage_node_p);

        // If CAS succeeds then just return
        if (ret == true) {
          break;
        } else {
          LOG_TRACE("Add garbage node CAS failed. Retry");
        }
      }  // while 1

      return;
    }

    /*
     * JoinEpoch() - Let current thread join this epoch
     *
     * The effect is that all memory deallocated on and after
     * current epoch will not be freed before current thread leaves
     *
     * NOTE: It is possible that prev_count < 0, because in ClearEpoch()
     * the cleaner thread will decrease the epoch counter by a large amount
     * to prevent this function using an epoch currently being recycled
     */
    inline EpochNode *JoinEpoch() {
    try_join_again:
      // We must make sure the epoch we join and the epoch we
      // return are the same one because the current point
      // could change in the middle of this function
      EpochNode *epoch_p = current_epoch_p;

      int64_t prev_count = epoch_p->active_thread_count.fetch_add(1);

      // We know epoch_p is now being cleaned, so need to read the
      // current epoch again because it must have been moved
      if (prev_count < 0) {
        // Consider the following sequence:
        //   0. Start with counter = 0
        //   1. Worker thread 1 fetch_add() -> return 0, OK
        //   2. GC thread fetch_sub() -> return positive, abort!
        //   3. Worker thread 2 fetch_add() -> return negative, retry!
        //   4. GC thread fetch_add() and aborts
        //   5. Worker thread 2 retries, and fetch_add() -> return 1, OK
        // This way the second worker thread actually incremented the epoch
        // counter twice
        epoch_p->active_thread_count.fetch_sub(1);

        goto try_join_again;
      }

      return epoch_p;
    }

    /*
     * LeaveEpoch() - Leave epoch a thread has once joined
     *
     * After an epoch has been cleared all memories allocated on
     * and before that epoch could safely be deallocated
     */
    inline void LeaveEpoch(EpochNode *epoch_p) {
      // This might return a negative value if the current epoch
      // is being cleaned
      epoch_p->active_thread_count.fetch_sub(1);

      return;
    }

    /*
     * PerformGarbageCollection() - Actual job of GC is done here
     *
     * We need to separate the GC loop and actual GC routine to enable
     * external threads calling the function while also allows BwTree maintains
     * its own GC thread using the loop
     */
    void PerformGarbageCollection() {
      ClearEpoch();
      CreateNewEpoch();

      return;
    }

    void FreeNode(BaseNode *node_p) {
      size_t freed_size = 0;
      switch (node_p->GetNodeType()) {
        case NodeType::ValueNode: {
          delete (ValueNode *)(node_p);
          freed_size = skiplist_p->size_of_value_node;
          break;
        }
        case NodeType::LeafNode: {
          // need to remove dummy value node
          delete (((LeafNode *)node_p)->head);
          delete (LeafNode *)(node_p);
          freed_size =
              skiplist_p->size_of_value_node + skiplist_p->size_of_leaf_node;
          break;
        }
        case NodeType::InnerNode: {
          delete (InnerNode *)(node_p);
          freed_size = skiplist_p->size_of_inner_node;
          break;
        }
        default:
          LOG_DEBUG("We never delete other types of nodes");
          break;
      }
    // Update memory used
    update_memory:
      size_t cur_memory_used = skiplist_p->memory_used;
      while (!__sync_bool_compare_and_swap(&skiplist_p->memory_used,
                                           cur_memory_used,
                                           cur_memory_used - freed_size)) {
        goto update_memory;
      }
      return;
    }

    /*
     * ClearEpoch() - Sweep the chain of epoch and free memory
     *
     * The minimum number of epoch we must maintain is 1 which means
     * when current epoch is the head epoch we should stop scanning
     *
     * NOTE: There is no race condition in this function since it is
     * only called by the cleaner thread
     */
    void ClearEpoch() {
      LOG_TRACE("Start to clear epoch");

      while (1) {
        // Even if current_epoch_p is nullptr, this should work
        if (head_epoch_p == current_epoch_p) {
          LOG_TRACE("Current epoch is head epoch. Do not clean");

          break;
        }

        // Since it could only be acquired and released by worker thread
        // the value must be >= 0
        int active_thread_count = head_epoch_p->active_thread_count.load();
        PL_ASSERT(active_thread_count >= 0);

        // If we have seen an epoch whose count is not zero then all
        // epochs after that are protected and we stop
        if (active_thread_count != 0) {
          LOG_TRACE("Head epoch is not empty. Return");

          break;
        }

        // If some thread joins the epoch between the previous branch
        // and the following fetch_sub(), then fetch_sub() returns a positive
        // number, which is the number of threads that have joined the epoch
        // since last epoch counter testing.

        if (head_epoch_p->active_thread_count.fetch_sub(MAX_THREAD_COUNT) > 0) {
          LOG_TRACE(
              "Some thread sneaks in after we have decided"
              " to clean. Return");

          // Must add it back to let the next round of cleaning correctly
          // identify empty epoch
          head_epoch_p->active_thread_count.fetch_add(MAX_THREAD_COUNT);

          break;
        }

        // After this point all fetch_add() on the epoch counter would return
        // a negative value which will cause re-read of current_epoch_p
        // to prevent joining an epoch that is being deleted

        // If the epoch has cleared we just loop through its garbage chain
        // and then free each delta chain

        const GarbageNode *next_garbage_node_p = nullptr;

        // Walk through its garbage chain
        for (const GarbageNode *garbage_node_p =
                 head_epoch_p->garbage_list_p.load();
             garbage_node_p != nullptr; garbage_node_p = next_garbage_node_p) {
          FreeNode(garbage_node_p->node_p);

          // Save the next pointer so that we could
          // delete current node directly
          next_garbage_node_p = garbage_node_p->next_p;

          // This invalidates any further reference to its
          // members (so we saved next pointer above)
          delete garbage_node_p;
        }  // for

        // First need to save this in order to delete current node
        // safely
        EpochNode *next_epoch_node_p = head_epoch_p->next_p;

        delete head_epoch_p;

        // Then advance to the next epoch
        // It is possible that head_epoch_p becomes nullptr
        // this happens during destruction, and should not
        // cause any problem since that case we also set current epoch
        // pointer to nullptr
        head_epoch_p = next_epoch_node_p;
      }  // while(1) through epoch nodes

      return;
    }

    /*
     * ThreadFunc() - The cleaner thread executes this every GC_INTERVAL ms
     *
     * This function exits when exit flag is set to true
     */
    void ThreadFunc() {
      // While the parent is still running
      // We do not worry about race condition here
      // since even if we missed one we could always
      // hit the correct value on next try
      while (exited_flag.load() == false) {
        // printf("Start new epoch cycle");
        PerformGarbageCollection();

        // Sleep for 50 ms
        std::chrono::milliseconds duration(GC_INTERVAL);
        std::this_thread::sleep_for(duration);
      }

      LOG_TRACE("exit flag is true; thread return");

      return;
    }

    /*
     * StartThread() - Start cleaner thread for garbage collection
     *
     * NOTE: This is not called in the constructor, and needs to be
     * called manually
     */
    void StartThread() {
      thread_p = new std::thread{[this]() { this->ThreadFunc(); }};

      return;
    }

  };  // Epoch manager

 private:
  // Used for finding the least significant bit
  const int MultiplyDeBruijnBitPosition[32] = {
      0,  1,  28, 2,  29, 14, 24, 3, 30, 22, 20, 15, 25, 17, 4,  8,
      31, 27, 13, 23, 21, 19, 16, 7, 26, 12, 18, 6,  11, 5,  10, 9};
};

}  // namespace index
}  // namespace peloton
