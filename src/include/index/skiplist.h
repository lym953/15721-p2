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
//namespace peloton {
//namespace index {
#define PL_ASSERT(x)
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
    bool deleted;
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

  /**
   * key compare equal.
   */
  inline bool KeyCmpEqual(const KeyType &key1, const KeyType &key2) const {
      return key_eq_obj(key1, key2);
  }


  /*
   * KeyCmpLessEqual() - Compare two key-value pair for <= relation
   */
  inline bool KeyValueCmpEqual(const KeyValuePair &kvp1,const KeyValuePair &kvp2) const {
      return (key_eq_obj(kvp1.first, kvp2.first) &&
                    value_eq_obj(kvp1.second, kvp2.second));
  }


  ////////////////////////////////////////////////////////////////////
  // Interface Method Implementation
  ////////////////////////////////////////////////////////////////////
<<<<<<< Updated upstream
  bool Insert(const KeyType &key, const ValueType &value);
=======

  bool Insert(const KeyType &key, const ValueType &value) {
    // Check whether we should insert the new entry
    auto it = Begin(key);
    while (!it.IsEnd() && key_eq_obj(it->first, key)) {
      if (duplicated_key) return false;
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
      for (int i = 1; i < levels; i++) {
        in_nodes[i]->key = key;
        in_nodes[i]->down = in_nodes[i - 1];
      }
      in_nodes[0]->key = key;
      in_nodes[0]->down = lf_node;
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


  /**
 * Implete delete operation.
 * perform logical deletion - mark the base node as deleted.
 * The physical deletion will be performed by garbage collection.
 * The DeleteEntry function should erase only the index entry matching the specific <key, value> pair.
 * Some edge cases: how about I after deletion, I have no nodes in this level? - how should I update this?
 * What if I delete the node in the middle level. - I can't find a prev node pointing to this.
 * should i fail this? Or should I retry?
 */

  bool Delete(const KeyValuePair &keyPair) {
  //printf("Delete this key\n");
  // Check if skiplist is empty
  if (IsEmpty()) return false;
  LeafNode* node_to_delete = Find(keyPair);
  //if we can't find such a node return null.
  if (node_to_delete == NULL) {
    return false;
  }

  //update value here.
  //if fails should we retry the delete operation?
  //or just return fail?
  //check whether bw_tree implements with any atomic value.
  bool success = __sync_bool_compare_and_swap(&(node_to_delete->deleted), true, false);
  if (!success) {
    return false;
  }

  //going up until we hit the top level for this.
  InnerNode* prev = NULL;
  while(node_to_delete != NULL) {
    prev = node_to_delete;
    node_to_delete = ()
  }
  /*
  //<the one with key and its predecessor.
  //in case max level changes. - int records the level.
  std::map<InnerNode*, int> starting_inner_nodes;
  //store the current levels next ones.
  std::set<void*> next_level;
  //find all the node entries that contain the key.
  //32 sets containing all the nodes that are not connected by the previous one.
  //if not in previous one's next, adds into it.
  KeyType key = keyPair.first;
  for(int level = max_level; level >= 1; level--) {
      //find the largest node that is less than the current key.
      void *curr_node = Search(key, level);
      //no such a key in the current level.
      if (curr_node == NULL) {
        continue;
      }
      //now the current should be the one that >= key.
      std::set<void*> tmp_next_level;
      //loop this level and check.
       while(curr_node != NULL) {
          //above base level.
          if (KeyCmpGreater(((InnerNode*)curr_node)->key, key)) {
            break;
          }

          //if is a starting node.
          if (next_level.find(curr_node) == next_level.end()) {
              //insert into the starting nodes.
              starting_inner_nodes.insert(std::make_pair((InnerNode*)curr_node, level));
              //insert the next level.
              tmp_next_level.insert((void*)(((InnerNode*)curr_node)->down));
          }
          //move to next one.
          curr_node = (void*)(((BaseNode*)curr_node)->next);
        }
        //swing the temp and this.
        next_level.clear();
        next_level = tmp_next_level;
    }
    //the highest tower node pointing to the key-value pair.
    void* start_node = NULL;
    //the level of that tower.
    int start_level = -1;
    //iterate through all the starting nodes.
    for(auto itr = starting_inner_nodes.begin();\
          itr != starting_inner_nodes.end(); ++itr) {
        int level = itr->second;
        void* next_node = itr->first;
        //traverse down.
        while(level > 0) {
            next_node = ((InnerNode*)next_node)->down;
            level--;
        }
        //the base one.
        if (next_node == (void*)node_to_delete) {
          start_node = (void*)(itr->first);
          start_level = itr->second;
          break;
        }
    }

    //if start node is null. then it means that the node is only at bottom.
    if (start_node == NULL) {
        start_node = (void*)node_to_delete;
        start_level = 0;
    }
    */
    //start to delete this node. search from top to bottom.
    //prev may be a normal inner node, or a head node.
    //but no matter of what, it should give you prev.
    for (int i = start_level; i >= 1; i--) {
      link_level_i:
        //find the node pointing to the current node.
        void *ptr = SearchNode(start_node, i);
        //possibily header node.
        if (ptr == NULL) {
          if (head_nodes[i].next == start_node && ((BaseNode*)start_node)->next == NULL) {
            int cur_max_level = max_level;
            if (cur_max_level == i) {
             //do we care if this set fails?
             //TODO: don't care if fails right now.
              __sync_bool_compare_and_swap(&max_level, cur_max_level, cur_max_level-1);
            }
          }
          //set ptr's next to my current's next.
          while (!__sync_bool_compare_and_swap(&(head_nodes[i].next),\
                                               (BaseNode*)start_node,\
                                                ((BaseNode*)start_node)->next)){
            goto link_level_i;
          }
        } else {
          //set ptr's next to my current's next.
          while (!__sync_bool_compare_and_swap(&(((InnerNode *)(ptr))->next),\
                                               (BaseNode*)start_node,\
                                                ((BaseNode*)start_node)->next)){
            goto link_level_i;
          }
        }
        //move to next level.
        start_node = (void*)((InnerNode*)start_node)->down;
    }

    // cas the bottom one.
    link_level_0:
      void *ptr = SearchNode(start_node, 0);
      if (ptr != NULL) {
        //we don't reduce max level here because it's already 10.
        while (!__sync_bool_compare_and_swap(&(((LeafNode *)ptr)->next), (BaseNode*)start_node,\
                                             ((BaseNode*)start_node)->next)) {
          goto link_level_0;
        }
      } else {
        //we don't reduce max level here because it's already 10.
        while (!__sync_bool_compare_and_swap(&head_nodes[0].next, (BaseNode*)start_node,\
                                             ((BaseNode*)start_node)->next)) {
          goto link_level_0;
        }
      }

    return true;
  }
>>>>>>> Stashed changes
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
<<<<<<< Updated upstream
  void PrintSkipList();
=======

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
   *   [level 0]: 3 -> 4 -> 4 -> 5 -> 5 -> 6
   *
   * Ex: Search(5, 0) returns a pointer to the second 4
   *   [level 0]: 3 -> 4 -> 4 -> 6 -> 6 -> 6
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

 /*****
 * We want to find the given keyValuePair to check whether it's in the skiplist.
 * return the exactly leafNode containing the key-value pair.
 **/
LeafNode *Find(const KeyValuePair &keyPair) {
  KeyType key = keyPair.first;
  // Check if skiplist is empty
  void *curr_node = Search(key, 0);
  
  //LeafNode* prev_node = curr_node;
  //traverse down to find the key value pair.
  while(curr_node != NULL) {
    //over.
    if (KeyCmpGreater(((LeafNode*)curr_node)->pair.first, key)) {
      return NULL;
    }
    //compare key-value pair.
    if (KeyValueCmpEqual(((LeafNode*)curr_node)->pair, keyPair)) {
        //if deleted.
        if (((LeafNode*)curr_node)->deleted) {
          return NULL;
        }
        //return prev_node;
        return (LeafNode*)curr_node;
    }
    //prev_node = curr_node;
    curr_node = ((LeafNode*)curr_node)->next;
  }
  return NULL;
}

//searchNode - to find a node in the skipList.
/*****
 * We want to find the given keyValuePair to check whether it's in the skiplist.
 * return the exactly leafNode containing the key-value pair.
 **/
void *SearchNode(const void* node, const int level) {
  void* prev = NULL;
  KeyType key;
  if (level == 0) {
    key = ((LeafNode*)node)->pair.first;
  } else {
    key = ((InnerNode*)node)->key;
  }
  prev = SearchLower(key, level);
  //we still want to search from start to avoid false positive.
  void* curr_node;
  //if we can't find such a node.
  if(prev == NULL) {
    curr_node = head_nodes[level].next;
  } else {
    curr_node = ((BaseNode*)prev)->next;
  }

  //start to find the node.
  while(curr_node != NULL) {
    if(level == 0) {
      if (KeyCmpGreater(((LeafNode*)curr_node)->pair.first, key)) {
        prev = NULL;
        break;
      }
    } else {
      if (KeyCmpGreater(((InnerNode*)curr_node)->key, key)) {
        prev = NULL;
        break;
      }
    }
    if(curr_node == node) {
      break;
    } 
    //move to next one.
    prev = curr_node;
    curr_node = ((BaseNode*)curr_node)->next;
  }
  return prev;
}
>>>>>>> Stashed changes

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

//}  // namespace index
//}  // namespace peloton
