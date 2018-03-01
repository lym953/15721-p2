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
    BaseNode *next = NULL;
  };

  class HeadNode : public BaseNode {};

  class InnerNode : public BaseNode {
   public:
    KeyType key;
    BaseNode *down;
    InnerNode *up;

   public:
    InnerNode(const KeyType &key) : key(key), down(NULL), up(NULL) {}
  };

  class ValueNode : public BaseNode {
   public:
    ValueType value;

   public:
    ValueNode(const ValueType &value) : value(value){};
  };

  class LeafNode : public BaseNode {
   public:
    KeyValuePair pair;  // will be removed in the future
    KeyType key;
    ValueNode *head;
    InnerNode *up;  // will be removed in the future
    bool deleted;   // will be removed in the future

   public:
    LeafNode(const KeyType &key, const ValueType &value)
        : key(key), head(NULL), up(NULL), deleted(false) {
      pair = std::make_pair(key, value);
    }

    LeafNode(const KeyType &key) : key(key), head(NULL) {}
  };

  //Used for garbage collection
  /*class InnerGCNode : public BaseNode {
    public:
      InnerNode* node;
    public:
      InnerGCNode(const InnerNode* node)
        : node(node) {};
  };

  class LeafGCNode : public BaseNode {
    public:
      LeafNode* node;
    public:
      LeafGCNode(const LeafNode* node)
        : node(node) {};
  };

  class ValueGCNode : public BaseNode {
    public:
      ValueNode* node;
    public:
      ValueGCNode(const ValueNode* node)
        : node(node) {};
  };*/

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
   * KeyCmpEqual() - Comapre two key pair for == relation
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
                              const ValueType &val2) const{
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
    // Create LeafNode and ValueNode and append
    LeafNode *lf_node = new LeafNode(key);
    ValueNode *dummy = new ValueNode(value);  // this value is useless
    ValueNode *v_node = new ValueNode(value);
    lf_node->head = dummy;
    dummy->next = v_node;

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
      return true;
    } else {
      // someone has insert this leafNode
      if (!duplicated_key) {
        delete lf_node;
        delete v_node;
        delete dummy;
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
        delete lf_node;
        delete v_node;
        delete dummy;
        return false;
      } else {
        // update head so that it points to you
        while (!__sync_bool_compare_and_swap(
                   &(((LeafNode *)leaf_start_insert)->head->next),
                   (ValueNode *)(v_node->next), v_node)) {
          goto search_place_to_insert;
        }
        delete lf_node;
        delete dummy;
        return true;
      }
    }
    return true;
  }

  /**
   * Implete delete operation.
   * perform logical deletion - mark the base node as deleted.
   * The physical deletion will be performed by garbage collection.
   * The DeleteEntry function should erase only the index entry matching the
   * specific <key, value> pair.
   */
  bool Delete(const KeyType &key, const ValueType &value) {
    // Check if skiplist is empty
    if (IsEmpty()) return false;
    //find the leafNode to delete
    LeafNode* leafNode = (LeafNode*)Search(key, 0);
    if (leafNode == NULL || !KeyCmpEqual(leafNode->key, key)) {
      return false;
    }
    //find the node to be deleted
    ValueNode* node_to_delete = SearchValueNode(leafNode, value, false);
    if(node_to_delete == NULL) {
      return false;
    }

    //delete this 
    delete_value_node:
      //start to cmp swap this.
      ValueNode* findPrev = SearchValueNode(leafNode, value, true);
      //this value already has been deleted by another thread.
      if (findPrev == NULL) {
        return false;
      }
      //cas this value node.
      while (!__sync_bool_compare_and_swap(&(findPrev->next), ((BaseNode*)node_to_delete), 
                                      node_to_delete->next)){
              goto delete_value_node;
      }

    //check whether we need to delete the whole branch.
    bool delete_branch = false;
    if(findPrev == leafNode->head && node_to_delete->next == NULL){
      delete_branch = true;
    }
    // start to delete this node. search from top to bottom.
    // prev may be a normal inner node, or a head node.
    // but no matter of what, it should give you prev.
    if (delete_branch) {
      void* start_node = NULL;
      //When I want to delete the top, I have to find one.
      //Search returns the first duplicate one.
      //if the returned doesn't have the key, it means it cannot be in the list.
      int start_level = -1;
      for(int i = max_level; i >= 0; i--) {
        //search all the levels until I got my node.
        start_node = Search(key, i);
        if (start_node != NULL) {
            if(i != 0) {
              if(KeyCmpEqual(((InnerNode*)start_node)->key, key)) {
                start_level = i;
                break;
              }
            } else {
              if (KeyCmpEqual(((LeafNode*)start_node)->key, key)) {
                start_level = i;
                break;
              }
            }
        }
      }
      for (int i = start_level; i >= 1; i--) {
        link_level_i:
          // find the node pointing to the current node.
          void *ptr = SearchNode(start_node, i);
          // possibily header node.
          if (ptr == NULL) {
            if (head_nodes[i].next == start_node &&
                ((BaseNode *)start_node)->next == NULL) {
              int cur_max_level = max_level;
              if (cur_max_level == i) {
                // do we care if this set fails?
                // TODO: don't care if fails right now.
                __sync_bool_compare_and_swap(&max_level, cur_max_level,
                                             cur_max_level - 1);
              }
            }
            // set ptr's next to my current's next.
            while (!__sync_bool_compare_and_swap(&(head_nodes[i].next),
                                                 (BaseNode *)start_node,
                                                 ((BaseNode *)start_node)->next)) {
              goto link_level_i;
            }
          } else {
            // set ptr's next to my current's next.
            while (!__sync_bool_compare_and_swap(&(((InnerNode *)(ptr))->next),
                                                 (BaseNode *)start_node,
                                                 ((BaseNode *)start_node)->next)) {
              goto link_level_i;
            }
          }
        // move to next level.
        start_node = (void *)((InnerNode *)start_node)->down;
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
          // we don't reduce max level here because it's already 0.
          while (!__sync_bool_compare_and_swap(&head_nodes[0].next,
                                               (BaseNode *)start_node,
                                               ((BaseNode *)start_node)->next)) {
            goto link_level_0;
          }
        }
    }
    //memory_pool.push_back((void *)node_to_delete);
    return true;
  }

  //  bool ConditionalInsert(const KeyType &key, const ValueType &value,
  //                         std::function<bool(const void *)> predicate,
  //                         bool *predicate_satisfied);
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
      key = ((LeafNode *)node)->pair.first;
    } else {
      key = ((InnerNode *)node)->key;
    }
    prev = SearchLower(key, level);
    // we still want to search from start to avoid false positive.
    void *curr_node;
    // if we can't find such a node.
    if (prev == NULL) {
      curr_node = head_nodes[level].next;
    } else {
      curr_node = ((BaseNode *)prev)->next;
    }

    // start to find the node.
    while (curr_node != NULL) {
      if (level == 0) {
        if (KeyCmpGreater(((LeafNode *)curr_node)->pair.first, key)) {
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
        break;
      }
      // move to next one.
      prev = curr_node;
      curr_node = ((BaseNode *)curr_node)->next;
    }
    return prev;
  }

  /***
   * This function wants to find the ValueNode to Delete. 
   * return NULL.
   * if prev_node is true, then it means that it wants to find the 
   */
  ValueNode* SearchValueNode(const LeafNode* leafNode, 
                                            const ValueType &value, 
                                            bool prev_node) {
    ValueNode* prev = leafNode->head;
    ValueNode* curr = (ValueNode*)(prev->next);
    while(curr != NULL) {
      //if we found the valueNode.
      if(ValueCmpEqual(curr->value, value)) {
          if(prev_node) {
            return prev;
          }
          else {
            return curr;
          }
      }
      //move to next one.
      prev = curr;
      curr = (ValueNode*)curr->next;
    }
    return NULL;
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

 private:
  // Used for finding the least significant bit
  const int MultiplyDeBruijnBitPosition[32] = {
      0,  1,  28, 2,  29, 14, 24, 3, 30, 22, 20, 15, 25, 17, 4,  8,
      31, 27, 13, 23, 21, 19, 16, 7, 26, 12, 18, 6,  11, 5,  10, 9};
};

}  // namespace index
}  // namespace peloton
