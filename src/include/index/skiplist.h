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

#define MAX_LEVEL 31

#define MARKED 0b1
#define UNMARKED 0b0

#define INVALID_VALUE 0x7FFFFFFF

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
  class ValueNode;
  class ForwardIterator;
  class ValueChain;
  class Node;

 public:
  // members
  Node *head;
  Node *tail;

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

    size_of_node = (sizeof(Node));
    size_of_value_node = (sizeof(ValueNode));
    size_of_data_node = (sizeof(DataNode));
    size_of_value_chain = (sizeof(ValueChain));

    LOG_DEBUG("size of nodes: Value %zu, Node %zu, DataNode %zu",
              size_of_value_node, size_of_value_node, size_of_data_node);

    head = new Node();
    tail = new Node();
    for (size_t i = 0; i < head->next.size(); i++) {
      head->next[i] = tail;
    }

    LOG_TRACE("Starting epoch manager thread...");
    // epoch_manager.StartThread();
  };

  // Destructor
  ~SkipList() {
    // Free alive nodes
    Node *ptr = head;
    while (ptr) {
      Node *temp = ptr;
      ptr = ptr->next[0];
      if (temp->GetNodeType() == NodeType::Node) {
        delete (Node *)temp;
      } else {
        delete (DataNode *)temp;
      }
    }
    LOG_DEBUG("size of nodes: Value %zu, Node %zu, DataNode %zu",
              size_of_value_node, size_of_value_node, size_of_data_node);
  }

 public:
  using KeyValuePair = std::pair<KeyType, ValueType>;

  using EpochNode = typename EpochManager::EpochNode;

  ///////////////////////////////////////////////////////////////////
  // Node Types
  ///////////////////////////////////////////////////////////////////
  enum class NodeType : short {
    BaseNode = 0,
    ValueNode = 1,
    Node = 2,
    DataNode = 3
  };

  class BaseNode {
   public:
    uint64_t succ = 0;
    NodeType type = NodeType::BaseNode;

   public:
    NodeType GetNodeType() { return type; }
    inline BaseNode *Next() { return (BaseNode *)GetNextFromSucc(succ); }
    inline int GetMarkBit() { return GetMarkBitFromSucc(succ); }
  };

  class ValueNode : public BaseNode {
   public:
    ValueType value;

   public:
    ValueNode(const ValueType &value) : value(value) {
      BaseNode::type = NodeType::ValueNode;
    }
  };

  ///////////////////////////////////////////////////////////////////
  // Node Class
  ///////////////////////////////////////////////////////////////////

  class Node : public BaseNode {
   public:
    std::vector<Node *> next;
    int top_level;

   public:
    // Constructor for sentinel nodes
    Node() {
      next.resize(MAX_LEVEL + 1);
      top_level = MAX_LEVEL;
      BaseNode::type = NodeType::Node;
    }
  };

  class DataNode : public Node {
   public:
    SkipList *list;
    KeyType key;
    ValueChain *value_chain;

   public:
    // constructor for ordinary nodes
    DataNode(SkipList *list, const KeyType &key, const ValueType &value,
             int height) {
      this->list = list;
      this->key = key;
      value_chain = new ValueChain(list, key, value);

    // Update memory used
    update_memory:
      size_t cur_memory_used = list->memory_used;
      while (!__sync_bool_compare_and_swap(
                 &(list->memory_used), cur_memory_used,
                 cur_memory_used + list->size_of_value_chain)) {
        goto update_memory;
      }

      Node::next.resize(height + 1);
      Node::top_level = height;
      BaseNode::type = NodeType::DataNode;
    }

    ~DataNode() { delete value_chain; }
  };
  ///////////////////////////////////////////////////////////////////
  // ValueChain Class
  ///////////////////////////////////////////////////////////////////
  /***
   * ValueChain class is essentially a lock-free linked list. In addition, it
   * has following properties:
   *
   * 1. It has a key field associated with it. A value in the ValueChain
   * represents a (key, value) pair.
   *
   * 2. Once a ValueChain becomes empty, it's frozen. A frozen ValueChain is not
   *allowed to add more values. Therefore, it doesn't have a default
   *constructor. To construct a ValueChain, you must provide an initial value.
   *
   */
  class ValueChain {
   public:
    SkipList *list;
    KeyType key;
    ValueNode *head;
    ValueNode *tail;

   public:
    class Window {
     public:
      ValueNode *pred;
      ValueNode *curr;
      Window(ValueNode *my_pred, ValueNode *my_curr) {
        pred = my_pred;
        curr = my_curr;
      }
    };

   public:
    /***
     * Constructor. It constructor a ValueChain with initial value = @value.
     */
    ValueChain(SkipList *list, const KeyType &key, const ValueType &value) {
      this->list = list;
      this->key = key;

      // Values in the head and tail are just placeholders.
      head = new ValueNode(value);
      tail = new ValueNode(value);
      ValueNode *first_value = new ValueNode(value);

      size_t memory_claimed = 3 * list->size_of_value_node;

    // Update memory used
    update_memory:
      size_t cur_memory_used = list->memory_used;
      while (!__sync_bool_compare_and_swap(&(list->memory_used),
                                           cur_memory_used,
                                           cur_memory_used + memory_claimed)) {
        goto update_memory;
      }

      head->succ = PackSucc(first_value, UNMARKED);
      first_value->succ = PackSucc(tail, UNMARKED);
    }

    ~ValueChain() {
      ValueNode *ptr = head;
      ValueNode *temp;
      while (ptr) {
        temp = ptr;
        ptr = (ValueNode *)ptr->Next();
        delete temp;
      }
    }

    bool AttempMark(BaseNode *curr, BaseNode *succ) {
      return __sync_bool_compare_and_swap(
          &(curr->succ), PackSucc(succ, UNMARKED), PackSucc(succ, MARKED));
    }

    void PrintValueChain() {
      std::cout << "(" << key << ", "
                << "[" << std::flush;
      ValueNode *ptr = (ValueNode *)head->Next();
      while (ptr != tail) {
        std::cout << ptr->value << ", ";
        ptr = (ValueNode *)ptr->Next();
      }
      std::cout << "])" << std::endl;
    }

    /***
     * Add the given value to the ValueChain if it doesn't exist.
     * @param value The value to be inserted.
     * @return True if successfully added the value. False otherwise.
     */
    bool Add(const ValueType &value) {
      EpochNode *epoch_node_p = list->epoch_manager.JoinEpoch();
      while (true) {
        Window window = Find(head, value);
        ValueNode *pred = window.pred;
        ValueNode *curr = window.curr;

        // Check whether the ValueChain is frozen.
        if (pred == head && curr == tail) {
          list->epoch_manager.LeaveEpoch(epoch_node_p);
          return false;
        }

        if (curr != tail && list->value_eq_obj(curr->value, value)) {
          // The value already exists.
          list->epoch_manager.LeaveEpoch(epoch_node_p);
          return false;
        } else {
          // The value doesn't exist. Attempt to add a new value node.
          ValueNode *node = new ValueNode(value);

        // Update memory used
        update_memory:
          size_t cur_memory_used = list->memory_used;
          while (!__sync_bool_compare_and_swap(
                     &(list->memory_used), cur_memory_used,
                     cur_memory_used + list->size_of_value_node)) {
            goto update_memory;
          }

          // Try to insert the new node into the ValueChain.
          node->succ = PackSucc(curr, UNMARKED);
          if (__sync_bool_compare_and_swap(&(pred->succ),
                                           PackSucc(curr, UNMARKED),
                                           PackSucc(node, UNMARKED))) {
            list->epoch_manager.LeaveEpoch(epoch_node_p);
            return true;
          } else {
            // pred has been changed. Need to search again.
            list->epoch_manager.AddGarbageNode(node);
          }
        }
      }
    }

    /***
     * Delete the given value from the ValueChain if it exists. It will first
     * marked the ValueNode to be logically deleted and attempt physical
     * removal.
     * @param value The value to be deleted.
     * @return True if successfully deleted the value. False otherwise.
     */
    bool Delete(const ValueType &value) {
      EpochNode *epoch_node_p = list->epoch_manager.JoinEpoch();
      bool snip;
      while (true) {
        Window window = Find(head, value);
        ValueNode *pred = window.pred;
        ValueNode *curr = window.curr;
        if (curr == tail || !list->value_eq_obj(curr->value, value)) {
          // The value doesn't exist.
          list->epoch_manager.LeaveEpoch(epoch_node_p);
          return false;
        } else {
          ValueNode *succ = (ValueNode *)curr->Next();
          // Try to marked the node as logically deleted. Once we succeed, we
          // are essentially done.
          snip = AttempMark(curr, succ);
          if (!snip) continue;

          // Attempt physical deletion. It doesn't matter if it fails because
          // Find() will help us with physical deletion.
          if (__sync_bool_compare_and_swap(&(pred->succ),
                                           PackSucc(curr, UNMARKED),
                                           PackSucc(succ, UNMARKED))) {
            list->epoch_manager.AddGarbageNode(curr);
          }
          list->epoch_manager.LeaveEpoch(epoch_node_p);
          return true;
        }
      }
    }

    /***
     * Given a value, search the ValueChain starting from @head and find two
     *nodes, pred and
     * curr, such that
     * if the value exists:
     *      curr->value == @value and pred->Next() == curr
     * if the value doesn't exist
     *      curr == tail and pred->Next() == curr
     *
     * As a side effect, it will physically removed nodes if it sees a marked
     *ValueNode.
     * @param head search starting point
     * @param value the value we want to find
     * @return a Window such that Window.curr->value == value or Window.curr ==
     * tail and Window.pred->Next() == Window.curr
     */
    Window Find(ValueNode *head, const ValueType &value) {
      EpochNode *epoch_node_p = list->epoch_manager.JoinEpoch();
      ValueNode *pred = NULL;
      ValueNode *curr = NULL;
      ValueNode *succ = NULL;
      uint64_t marked;
      bool snip;
    retry:
      while (true) {
        pred = head;
        PL_ASSERT(pred);
        curr = (ValueNode *)pred->Next();
        while (true) {
          succ = (ValueNode *)GetAddressAndMarkBit((void *)curr->succ, marked);
          while (marked) {
            snip = __sync_bool_compare_and_swap(&(pred->succ),
                                                PackSucc(curr, UNMARKED),
                                                PackSucc(succ, UNMARKED));
            if (!snip) goto retry;
            list->epoch_manager.AddGarbageNode(curr);
            curr = succ;
            succ =
                (ValueNode *)GetAddressAndMarkBit((void *)curr->succ, marked);
          }
          if (curr == tail || list->value_eq_obj(curr->value, value)) {
            list->epoch_manager.LeaveEpoch(epoch_node_p);
            return Window(pred, curr);
          }
          pred = curr;
          curr = succ;
          PL_ASSERT(pred != tail);
          PL_ASSERT(curr != NULL);
        }
      }
    }

    bool IsFrozen() { return head->Next() == tail; }
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

  /////////////////////////////////////////////////////////////
  // Linked list helper functions
  ////////////////////////////////////////////////////////////
  /*
   * GetMarkBitFromSucc() - Get "mark" bit from successor field
   */
  inline static uint64_t GetMarkBitFromSucc(uint64_t succ) {
    return succ & 0b1;
  }

  /*
   * GetNextFromSucc() - Get "next" pointer from successor field
   */
  inline static void *GetNextFromSucc(uint64_t succ) {
    return (void *)(succ & ~0b1);
  }

  /*
   * PackSucc() - Pack "next" pointer and "mark" bit into a 64-bit successor
   * field
   */
  inline static uint64_t PackSucc(void *next, uint64_t marked) {
    return ((uint64_t)next) | marked;
  }

  /**
   * Attempt to mark the given address.
   */
  inline static bool AttempMark(Node *&address, Node *expected) {
    return __sync_bool_compare_and_swap(&address, PackSucc(expected, UNMARKED),
                                        PackSucc(expected, MARKED));
  }

  /**
   * A combination of GetMarkBitFromSucc() and GetNextFromSucc().
   * It sets @marked and returns the real address.
   */
  inline static void *GetAddressAndMarkBit(void *address, uint64_t &marked) {
    marked = (uint64_t)address & 0b1;
    return (void *)((uint64_t)address & ~0b1);
  }

  ////////////////////////////////////////////////////////////////////
  // Interface Method Implementation
  ////////////////////////////////////////////////////////////////////

  /**
   * Attempt to insert (key, value) pair into the skiplist.
   * @param key
   * @param value
   * @return False if key already exists and we don't allow duplicated
   * key, or when duplicated keys are allowed, the (key, value) pair already
   * exists. True otherwise.
   */
  bool Insert(const KeyType &key, const ValueType &value) {
    EpochNode *epoch_node_p = epoch_manager.JoinEpoch();

    // Get random height by finding the last significant bit.
    int v = rand();
    int top_level =
        MultiplyDeBruijnBitPosition[((uint32_t)((v & -v) * 0x077CB531U)) >> 27];

    int bottom_level = 0;
    std::vector<Node *> preds(MAX_LEVEL + 1);
    std::vector<Node *> succs(MAX_LEVEL + 1);

    while (true) {
    retry:
      bool temp = Find(key, preds, succs);
      bool found = temp;
      if (found) {
        // We have found the Node but be aware of that the ValueChain of the
        // Node might be frozen, which means that the Node is about to be
        // logically deleted.
        if (!duplicated_key) {
          if (!((DataNode *)succs[bottom_level])->value_chain->IsFrozen()) {
            // The ValueChain is not frozen. Since duplicated keys are not
            // allowed. We give up.
            epoch_manager.LeaveEpoch(epoch_node_p);
            return false;
          } else {
            // The ValueChain is frozen. Be patient and wait until the Node to
            // be logically deleted.
            goto retry;
          }
        } else {
          // We allow duplicated key. Try to insert the value into the
          // ValueChain.
          bool success =
              ((DataNode *)succs[bottom_level])->value_chain->Add(value);
          if (success) {
            // Successfully inserted the value. Done.
            epoch_manager.LeaveEpoch(epoch_node_p);
            return true;
          } else {
            // Insertion failed. It's either because its frozen or the value
            // alreay exists
            if (((DataNode *)succs[bottom_level])->value_chain->IsFrozen()) {
              // The ValueChain is frozen. Be patient and wait until the Node to
              // be logically deleted.
              goto retry;
            } else {
              // It must be the case that value already exists.
              epoch_manager.LeaveEpoch(epoch_node_p);
              return false;
            }
          }
        }
      } else {  // We did not find such Node, need to create a new one.

        DataNode *new_node = new DataNode(this, key, value, top_level);

      // Update memory used
      update_memory:
        size_t cur_memory_used = memory_used;
        while (!__sync_bool_compare_and_swap(
                   &memory_used, cur_memory_used,
                   cur_memory_used + size_of_data_node)) {
          goto update_memory;
        }

        // Link the new Node to successors.
        for (int level = bottom_level; level <= top_level; level++) {
          Node *succ = succs[level];
          new_node->next[level] = (Node *)PackSucc(succ, UNMARKED);
        }
        Node *pred = preds[bottom_level];
        Node *succ = succs[bottom_level];
        new_node->next[bottom_level] = (Node *)PackSucc(succ, UNMARKED);

        // Link predecessors to the new Node.
        if (!__sync_bool_compare_and_swap(&(pred->next[bottom_level]),
                                          PackSucc(succ, UNMARKED),
                                          PackSucc(new_node, UNMARKED))) {
          epoch_manager.AddGarbageNode(new_node);
          continue;
        }
        for (int level = bottom_level + 1; level <= top_level; level++) {
          while (true) {
            pred = preds[level];
            succ = succs[level];
            if (__sync_bool_compare_and_swap(&(pred->next[level]),
                                             PackSucc(succ, UNMARKED),
                                             PackSucc(new_node, UNMARKED)))
              break;
            // Failed linking. It must be that preds or succs have been changed.
            // Try to find them again.
            Find(key, preds, succs);
          }
        }
        epoch_manager.LeaveEpoch(epoch_node_p);
        return true;
      }
    }
  }

  /**
   * Attempt to delete (key, value) pair from the skiplist. If we found such
   * pair we remove the value from the ValueChain first. Then if the ValueChain
   * is frozen, then it means that the Node that contains the ValueChain needs
   * to be deleted. It will try mark the Node to be logically removed and attemp
   * physical removal.
   * @param key
   * @param value
   * @return False if key the (key,value) pair doesn't exist. True otherwise.
   */
  bool Delete(const KeyType &key, const ValueType &value) {
    EpochNode *epoch_node_p = epoch_manager.JoinEpoch();
    int bottom_level = 0;
    std::vector<Node *> preds(MAX_LEVEL + 1);
    std::vector<Node *> succs(MAX_LEVEL + 1);
    Node *succ;
    while (true) {
      bool found = Find(key, preds, succs);
      if (!found) {
        epoch_manager.LeaveEpoch(epoch_node_p);
        return false;
      }
      // Try to delete the value first
      bool succeed =
          ((DataNode *)succs[bottom_level])->value_chain->Delete(value);
      if (!succeed) {
        // Deletion failed. The value doesn't exist. Done.
        epoch_manager.LeaveEpoch(epoch_node_p);
        return false;
      } else if (((DataNode *)succs[bottom_level])->value_chain->IsFrozen()) {
        // After you delete the value, the value_chain is frozen. Need to mark
        // the Node to be logically deleted.
        Node *node_to_remove = succs[bottom_level];

        // Try to mark higher levels.
        for (int level = node_to_remove->top_level; level >= bottom_level + 1;
             level--) {
          uint64_t marked;
          succ =
              (Node *)GetAddressAndMarkBit(node_to_remove->next[level], marked);
          while (!marked) {
            AttempMark(node_to_remove->next[level], succ);
            succ = (Node *)GetAddressAndMarkBit(node_to_remove->next[level],
                                                marked);
          }
        }

        // Try to mark bottom level.
        uint64_t marked;
        succ = (Node *)GetAddressAndMarkBit(node_to_remove->next[bottom_level],
                                            marked);
        while (true) {
          bool i_marked_it = __sync_bool_compare_and_swap(
              &(node_to_remove->next[bottom_level]), PackSucc(succ, UNMARKED),
              PackSucc(succ, MARKED));
          succ = (Node *)GetAddressAndMarkBit(
              node_to_remove->next[bottom_level], marked);
          if (i_marked_it) {
            // Once we marked it call Find() to physically delete it. We just
            // want the side effect of Find().
            Find(key, preds, succs);
            epoch_manager.LeaveEpoch(epoch_node_p);
            return true;
          } else if (marked) {
            // Someone else marked (logically deleted) it. I should return false
            // because I didn't mark (logically delete) it.
            epoch_manager.LeaveEpoch(epoch_node_p);
            return false;
          }
        }
      } else {
        // Successfully delete the value but the value_chain is not frozen.
        epoch_manager.LeaveEpoch(epoch_node_p);
        return true;
      }
    }
  }

  /**
   * Given a key, it fills preds with Nodes whose keys are < the given key and
   * succs with Nodes whose keys are >= the given key. head is considered < all
   * Nodes and tail is considered > all Nodes.
   *
   * This function has a side effect: it physically removes marked
   * (logically deleted) Nodes as it's searching.
   *
   * It returns whether we found a Node whose key == the given key.
   * @param key
   * @param preds
   * @param succs
   * @return True if we found such Node. False otherwise.
   */
  bool Find(const KeyType &key, std::vector<Node *> &preds,
            std::vector<Node *> &succs) {
    EpochNode *epoch_node_p = epoch_manager.JoinEpoch();
    int bottom_level = 0;
    uint64_t marked;
    bool snip = false;
    Node *pred = NULL;
    Node *curr = NULL;
    Node *succ = NULL;
  retry:
    while (true) {
      pred = head;
      for (int level = MAX_LEVEL; level >= bottom_level; level--) {
        curr = (Node *)GetNextFromSucc((uint64_t)pred->next[level]);
        while (true) {
          succ = (Node *)GetAddressAndMarkBit(curr->next[level], marked);
          while (marked) {
            // Find a marked Node. Try to physically delete it.
            snip = __sync_bool_compare_and_swap(&(pred->next[level]),
                                                PackSucc(curr, UNMARKED),
                                                PackSucc(succ, UNMARKED));
            if (!snip) goto retry;
            if (level == bottom_level) {
              epoch_manager.AddGarbageNode(curr);
            }
            curr = (Node *)GetNextFromSucc((uint64_t)pred->next[level]);
            succ = (Node *)GetAddressAndMarkBit(curr->next[level], marked);
          }
          if (curr != tail && KeyCmpLess(((DataNode *)curr)->key, key)) {
            pred = curr;
            curr = succ;
          } else {
            break;
          }
        }
        preds[level] = pred;
        succs[level] = curr;
      }
      epoch_manager.LeaveEpoch(epoch_node_p);
      if (curr == tail) {
        return false;
      } else {
        return KeyCmpEqual(((DataNode *)curr)->key, key);
      }
    }
  }

  /**
   * It fills the value_list with all values asscoated with the search_key.
   *
   * @param search_key
   * @param value_list
   */
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
    Node *node = NULL;
    ValueNode *val_node = NULL;
    SKIPLIST_TYPE *list_p;

   public:
    /*
     * Constructor
     *
     * The iterator will point to the first element in the list, or become an
     * end iterator if the list is empty.
     */
    ForwardIterator(SKIPLIST_TYPE *p_list_p) : list_p{p_list_p} {
      node = list_p->head->next[0];
      if (!IsEnd()) {
        val_node = (ValueNode *)((DataNode *)node)->value_chain->head->Next();
      }
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
    inline bool IsEnd() const { return node == list_p->tail; }

    /*
     * LowerBound() - Find data item whose key >= start_key
     */
    void LowerBound(const KeyType &start_key) {
      std::vector<Node *> preds(MAX_LEVEL + 1);
      std::vector<Node *> succs(MAX_LEVEL + 1);

      // succs[0].key >= key, or succ[0] == tail
      list_p->Find(start_key, preds, succs);

      node = succs[0];
      if (!IsEnd()) {
        val_node = (ValueNode *)((DataNode *)node)->value_chain->head->Next();
      }
      MoveAheadToUndeletedNode();
    }

    /*
     * GetKey() - Get the key pointed by the iterator
     *
     * The caller is responsible for checking whether the iterator has
     * reached its end. If yes then assertion will fail.
     */
    inline const KeyType GetKey() {
      PL_ASSERT(!IsEnd());
      return ((DataNode *)node)->key;
    }

    /*
     * GetValue() - Get the value pointed by the iterator
     *
     * The caller is responsible for checking whether the iterator has
     * reached its end. If yes then assertion will fail.
     */
    inline const ValueType GetValue() {
      // Not reached the end of skiplist
      PL_ASSERT(!IsEnd());
      // Not reached the end of value chain
      PL_ASSERT(val_node != ((DataNode *)node)->value_chain->tail);

      return val_node->value;
    }

    /*
     * Prefix operator++ - Move the iterator ahead
     *
     * The caller is responsible for checking whether the iterator has
     reached
     * its end.
     */
    inline ForwardIterator &operator++() {
      MoveAheadByOne();
      return *this;
    }

    /*
     * MoveAheadByOne() - Move the iterator ahead by one
     *
     * Before invocation, the iterator should be pointing to a valid data
     * item.
     * The caller is responsible for checking whether the iterator has
     * reached its end. If iterator has reached end then assertion fails.
     */
    inline void MoveAheadByOne() {
      // Not reached the end of skiplist
      PL_ASSERT(!IsEnd());
      // Not reached the end of value chain
      PL_ASSERT(val_node != ((DataNode *)node)->value_chain->tail);

      val_node = (ValueNode *)val_node->Next();
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
      if (IsEnd()) {
        return;
      }

      while (true) {
        if (node->GetMarkBit() ||
            val_node == ((DataNode *)node)->value_chain->tail) {
          // The node has been logically deleted, or we have reached the end of
          // value chain. Advance node.
          node = node->next[0];
          // Reach the end of skiplist
          if (IsEnd()) {
            return;
          }
          val_node = (ValueNode *)((DataNode *)node)->value_chain->head->Next();
          PL_ASSERT(val_node->type == NodeType::ValueNode);
        } else if (val_node->GetMarkBit()) {
          // Value node has been deleted. Advance value node.
          val_node = (ValueNode *)val_node->Next();
        } else {
          // Pointing to an undeleted node right now
          return;
        }
      }
    }
  };

  ///////////////////////////////////////////////////////////////////
  // Utility Funciton
  ///////////////////////////////////////////////////////////////////
  void PrintSkipList() {
    Node *ptr = head->next[0];
    int count = 0;
    while (ptr != tail) {
      std::cout << ptr << ": ";
      ((DataNode *)ptr)->value_chain->PrintValueChain();

      ptr = ptr->next[0];
      count++;
    }
    printf("Total: %d\n", count);
  }

 public:
  const bool duplicated_key;
  // Key comparator
  const KeyComparator key_cmp_obj;

  // Raw key eq checker
  const KeyEqualityChecker key_eq_obj;

  const ValueEqualityChecker value_eq_obj;

  EpochManager epoch_manager;

  size_t size_of_value_node;

  size_t size_of_node;

  size_t size_of_data_node;

  size_t size_of_value_chain;

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
      CreateNewEpoch();
      ClearEpoch();

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
        case NodeType::Node: {
          // need to remove dummy value node
          delete (Node *)(node_p);
          freed_size = skiplist_p->size_of_node;
          break;
        }
        case NodeType::DataNode: {
          delete ((DataNode *)(node_p));
          freed_size = skiplist_p->size_of_data_node;
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
        CreateNewEpoch();

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
