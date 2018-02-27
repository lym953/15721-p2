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
#include <set>

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

/**
 * Implete delete operation.
 * perform logical deletion - mark the base node as deleted.
 * The physical deletion will be performed by garbage collection.
 * The DeleteEntry function should erase only the index entry matching the specific <key, value> pair.
 * Some edge cases: how about I after deletion, I have no nodes in this level? - how should I update this?
 * What if I delete the node in the middle level. - I can't find a prev node pointing to this.
 * should i fail this? Or should I retry?
 */
SKIPLIST_TEMPLATE_ARGUMENTS
bool SKIPLIST_TYPE::Delete(const &KeyValuePair keyPair) {
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
  bool success = __sync_bool_compare_and_swap(&(node_to_delete.deleted), true, false);
  if (!success) {
    return false;
  }
  //<the one with key and its predecessor.
  //in case max level changes. - int records the level.
  std::map<InnerNode*, int> starting_inner_nodes;
  std::vector<LeafNode*> starting_leaf_nodes;
  //store the current levels next ones.
  std:set<void*> next_level;
  //find all the node entries that contain the key.
  //32 sets containing all the nodes that are not connected by the previous one.
  //if not in previous one's next, adds into it.
  KeyType key = keyPair->pair.first;
  for(int level = max_level; level >= 0; level--) {
      //find the largest node that is less than the current key.
      void *prev = SearchDown(key, level);
      void* curr_node = (void*) prev->next;
      //now the current should be the one that >= key.
      std:set<void*> tmp_next_level;
      //loop this level and check.
       while(curr_node != NULL) {
          //if base level.
          if (level == 0) {
            if (KeyCmpGreater((LeafNode*)curr_node->pair.first, key)) {
              break;
            }

            //if is a starting node.
            if (next_level.find(curr_node) == next_level.end()) {
                //insert into the starting nodes.
                starting_leaf_nodes.insert((LeafNode*)curr_node);
                //we don't have next level at all.
            }
          } else {
            //above base level.
            if (KeyCmpGreater((InnerNode*)curr_node->key, key)) {
              break;
            }

            //if is a starting node.
            if (next_level.find(curr_node) == next_level.end()) {
                //insert into the starting nodes.
                starting_inner_nodes.insert(std::make_pair((InnerNode*)curr_node, level));
                //insert the next level.
                tmp_next_level.insert((void*)((InnerNode*)curr_node->down));
            }
          }
          //move to next one.
          curr_node = (void*)curr_node->next;
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
    for(std::map<InnerNode*, int>::iterator itr = starting_inner_nodes.begin(); \
          itr != starting_inner_nodes.end(); ++itr) {
        int level = *iter->second;
        void* next_node = *itr->first;
        //traverse down.
        while(level > 0) {
            next_node = (InnerNode*)next_node->down;
            level--;
        }
        //the base one.
        if (KeyValueCmpEqual((LeafNode*)next_node->pair, keyPair)) {
          start_node = (void*)*iter->first;
          start_level = *iter->second;
          break;
        }
    }
    //if can't find in the middle - just leaf node.
    if (start_node == NULL) {
        //iterate through all the starting nodes.
        for(std::vector<LeafNode*>::iterator itr = starting_leaf_nodes.begin(); \
              itr != starting_leaf_nodes.end(); ++itr) {
            LeafNode* tmp_start_node = *itr;
            //record the start node and the start level.
            if (KeyValueCmpEqual(tmp_start_node->pair, keyPair)) {
              start_node = (void*)tmp_start_node;
              start_level = 0;
              break;
            }
        }
    }

    //start to delete this node. search from top to bottom.
    //prev may be a normal inner node, or a head node.
    //but no matter of what, it should give you prev.
    for (int i = start_level; i >= 1; i--) {
      link_level_i:
        void *ptr = SearchNode(key, i);
        //if this ptr is a header node & reduce_level isn't true in current one.
        if (ptr == (void*)head_nodes[i]) {
           int cur_max_level = max_level;
           if (cur_max_level == i) {
             //do we care if this set fails?
             //TODO: don't care if fails right now.
              __sync_bool_compare_and_swap(&max_level, cur_max_level, cur_max_level-1);
           }
        }
        //set ptr's next to my current's next.
        while (!__sync_bool_compare_and_swap(&(((InnerNode *)(ptr))->next),\
                                               (BaseNode*)start_node,\
                                                start_node->next)){
           goto link_level_i;
        }
        //move to next level.
        start_node = (void*)start_node->down;
    }

    // cas the bottom one.
    link_level_0:
      void *ptr = SearchNode(key, i);
      //we don't reduce max level here because it's already 10.
      while (!__sync_bool_compare_and_swap(&(((LeafNode *)ptr)->next), (BaseNode*)start_node,\
                                             start_node->next)) {
          goto link_level_0;
      }
    return true;
}



/** 
 * This helper function helps you to find the key that is largest, strictly less than key.
 */
SKIPLIST_TEMPLATE_ARGUMENTS
void *SKIPLIST_TYPE::SearchDown(const KeyType &key, int level) {
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
SKIPLIST_TEMPLATE_ARGUMENTS
LeafNode *SKIPLIST_TYPE::Find(const &KeyValuePair keyPair) {
  // Check if skiplist is empty
  void *prev = SearchDown(key, 0);

  //if nothing finds.
  if(prev == NULL) {
    return NULL;
  }

  //if the next one is null or the next ones' key is not the key we want.
  LeafNode* curr_node = (LeafNode*) prev->next;
  if (curr_node == NULL || !KeyCmpEqual((LeafNode*)prev->pair.first, key)) {
    return NULL;
  }
  
  //LeafNode* prev_node = curr_node;
  //traverse down to find the key value pair.
  while(curr_node != NULL) {
    //over.
    if (KeyCmpGreater(curr_node->pair.first, key)) {
      return NULL;
    }
    //compare key-value pair.
    if (KeyValueCmpEqual(curr_node->pair, keyValuePair)) {
        //if deleted.
        if (curr_node->deleted) {
          return NULL;
        }
        //return prev_node;
        return curr_node;
    }
    //prev_node = curr_node;
    curr_node = (LeafNode*)curr_node->next;
  }
  return NULL;
}

//searchNode - to find a node in the skipList.
/*****
 * We want to find the given keyValuePair to check whether it's in the skiplist.
 * return the exactly leafNode containing the key-value pair.
 **/
SKIPLIST_TEMPLATE_ARGUMENTS
void *SKIPLIST_TYPE::searchNode(const void* node, const int level) {
  void* prev = NULL;
  KeyType key;
  if (level == 0) {
    key = (LeafNode*)node->pair.first;
  } else {
    key = (InnerNode*)node->key;
  }
  prev = SearchDown(key, level);
  //if we can't find such a node.
  if(prev == NULL) {
    return NULL;
  }

  void* curr_node = prev->next;
  if (curr_node == NULL) {
    return NULL;
  }

  if (level == 0) {
    if (KeyCmpGreater((LeafNode*) curr_node->pair.first, key)) {
      return NULL;
    }
  }

  if (level != 0) {
    if (KeyCmpGreater((InnerNode*) curr_node->key, key)) {
      return NULL;
    }
  }

  //start to find the node.
  while(curr_node != NULL) {
    if(level == 0) {
      if (KeyCmpGreater((LeafNode*)curr_node->pair.first, key)) {
        prev = NULL;
        break;
      }
    } else {
      if (KeyCmpGreater((InnerNode*)curr_node->key, key)) {
        prev = NULL;
        break;
      }
    }
    if(curr_node == node) {
      break;
    } 
    //move to next one.
    prev = curr_node;
    curr_node = curr_node->next;
  }
  return prev;
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
