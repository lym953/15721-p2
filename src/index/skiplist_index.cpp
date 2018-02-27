//===----------------------------------------------------------------------===//
//
//                         Peloton
//
// skiplist_index.cpp
//
// Identification: src/index/skiplist_index.cpp
//
// Copyright (c) 2015-17, Carnegie Mellon University Database Group
//
//===----------------------------------------------------------------------===//
#include "index/skiplist_index.h"

#include "common/logger.h"
#include "index/index_key.h"
#include "index/scan_optimizer.h"
#include "statistics/stats_aggregator.h"
#include "storage/tuple.h"

namespace peloton {
namespace index {

SKIPLIST_TEMPLATE_ARGUMENTS
SKIPLIST_INDEX_TYPE::SkipListIndex(IndexMetadata *metadata)
    :  // Base class
      Index{metadata},
      // Key "less than" relation comparator
      comparator{},
      // Key equality checker
      equals{},

      container{metadata->HasUniqueKeys(), comparator, equals} {
  return;
}

SKIPLIST_TEMPLATE_ARGUMENTS
SKIPLIST_INDEX_TYPE::~SkipListIndex() {}

/*
 * InsertEntry() - insert a key-value pair into the map
 *
 * If the key value pair already exists in the map, just return false
 */
SKIPLIST_TEMPLATE_ARGUMENTS
bool SKIPLIST_INDEX_TYPE::InsertEntry(const storage::Tuple *key,
                                      ItemPointer *value) {
  KeyType index_key;
  index_key.SetFromKey(key);

  bool ret = container.Insert(index_key, value);

  LOG_TRACE("DeleteEntry(key=%s, val=%s) [%s]", index_key.GetInfo().c_str(),
            IndexUtil::GetInfo(value).c_str(), (ret ? "SUCCESS" : "FAIL"));

  return ret;
}

/*
 * DeleteEntry() - Removes a key-value pair
 *
 * If the key-value pair does not exists yet in the map return false
 */
SKIPLIST_TEMPLATE_ARGUMENTS
bool SKIPLIST_INDEX_TYPE::DeleteEntry(
    UNUSED_ATTRIBUTE const storage::Tuple *key,
    UNUSED_ATTRIBUTE ItemPointer *value) {
  bool ret = false;
  // TODO: Add your implementation here
  return ret;
}

SKIPLIST_TEMPLATE_ARGUMENTS
bool SKIPLIST_INDEX_TYPE::CondInsertEntry(
    const storage::Tuple *key, ItemPointer *value,
    std::function<bool(const void *)> predicate) {
  std::vector<ValueType> values;
  ScanKey(key, values);
  for (size_t i = 0; i < values.size(); i++) {
    if (predicate(values[i])) return false;
  }
  InsertEntry(key, value);
  return true;
}

/*
 * Scan() - Scans a range inside the index using index scan optimizer
 *
 */
SKIPLIST_TEMPLATE_ARGUMENTS
void SKIPLIST_INDEX_TYPE::Scan(
    UNUSED_ATTRIBUTE const std::vector<type::Value> &value_list,
    UNUSED_ATTRIBUTE const std::vector<oid_t> &tuple_column_id_list,
    UNUSED_ATTRIBUTE const std::vector<ExpressionType> &expr_list,
    ScanDirectionType scan_direction, std::vector<ValueType> &result,
    const ConjunctionScanPredicate *csp_p) {
  if (scan_direction == ScanDirectionType::INVALID) {
    throw Exception("Invalid scan direction \n");
  }

  LOG_TRACE("Scan() Point Query = %d; Full Scan = %d ", csp_p->IsPointQuery(),
            csp_p->IsFullIndexScan());

  if (csp_p->IsPointQuery()) {
    const storage::Tuple *point_query_key_p = csp_p->GetPointQueryKey();

    KeyType point_query_key;
    point_query_key.SetFromKey(point_query_key_p);
    container.GetValue(point_query_key, result);
  } else if (csp_p->IsFullIndexScan()) {
    for (auto it = container.Begin(); !it.IsEnd(); ++it) {
      result.push_back(it->second);
    }
  } else {
    const storage::Tuple *low_key_p = csp_p->GetLowKey();
    const storage::Tuple *high_key_p = csp_p->GetHighKey();

    LOG_TRACE("Partial scan low key: %s\n high key: %s",
              low_key_p->GetInfo().c_str(), high_key_p->GetInfo().c_str());

    KeyType index_low_key;
    KeyType index_high_key;
    index_low_key.SetFromKey(low_key_p);
    index_high_key.SetFromKey(high_key_p);

    // We use skiplist Begin() to first reach the lower bound
    // of the search key
    for (auto it = container.Begin(index_low_key);
         !it.IsEnd() && container.KeyCmpLessEqual(it->first, index_high_key);
         ++it) {
      result.push_back(it->second);
    }
  }  // if is full scan

  if (scan_direction == ScanDirectionType::BACKWARD) {
    std::reverse(result.begin(), result.end());
  }

  return;
}

/*
 * ScanLimit() - Scan the index with predicate and limit/offset
 *
 */
SKIPLIST_TEMPLATE_ARGUMENTS
void SKIPLIST_INDEX_TYPE::ScanLimit(
    UNUSED_ATTRIBUTE const std::vector<type::Value> &value_list,
    UNUSED_ATTRIBUTE const std::vector<oid_t> &tuple_column_id_list,
    UNUSED_ATTRIBUTE const std::vector<ExpressionType> &expr_list,
    UNUSED_ATTRIBUTE ScanDirectionType scan_direction,
    UNUSED_ATTRIBUTE std::vector<ValueType> &result,
    UNUSED_ATTRIBUTE const ConjunctionScanPredicate *csp_p,
    UNUSED_ATTRIBUTE uint64_t limit, UNUSED_ATTRIBUTE uint64_t offset) {
  if (scan_direction == ScanDirectionType::INVALID) {
    throw Exception("Invalid scan direction \n");
  }

  LOG_TRACE("Scan() Point Query = %d; Full Scan = %d ", csp_p->IsPointQuery(),
            csp_p->IsFullIndexScan());

  if (csp_p->IsPointQuery()) {
    const storage::Tuple *point_query_key_p = csp_p->GetPointQueryKey();

    KeyType point_query_key;
    point_query_key.SetFromKey(point_query_key_p);

    // Find the first node that matches the search key
    auto it = container.Begin(point_query_key);

    if (scan_direction == ScanDirectionType::FORWARD) {
      // Case 1.1: point query + forward scan

      // Skip some nodes to reach offset
      for (uint64_t i = 0; i < offset; i++, ++it) {
        if (it.IsEnd() || !container.key_eq_obj(it->first, point_query_key)) {
          return;
        }
      }

      // Collect results
      for (uint64_t i = 0; i < limit && !it.IsEnd() &&
                               container.key_eq_obj(it->first, point_query_key);
           i++, ++it) {
        result.push_back(it->second);
      }
    } else {
      // Case 1.2: point query + backward scan

      std::queue<ValueType> result_queue;

      // Collect the first (limit + offset) nodes
      for (uint64_t i = 0; i < limit + offset && !it.IsEnd() &&
                               container.key_eq_obj(it->first, point_query_key);
           i++, ++it) {
        result_queue.push(it->second);
      }

      // Translate the window until it reaches the end of the list or the right
      // end of window does not satiafy the query criterion
      while (!it.IsEnd() && container.key_eq_obj(it->first, point_query_key)) {
        result_queue.pop();
        result_queue.push(it->second);
        ++it;
      }

      // Dump needed result from the queue to the vector
      uint64_t result_size = MIN(limit, result_queue.size());
      for (uint64_t i = 0; i < result_size; i++) {
        result.push_back(result_queue.front());
        result_queue.pop();
      }
      std::reverse(result.begin(), result.end());
    }

  } else if (csp_p->IsFullIndexScan()) {
    auto it = container.Begin();

    if (scan_direction == ScanDirectionType::FORWARD) {
      // Case 2.1: full scan + forward scan

      // Skip some nodes to reach offset
      for (uint64_t i = 0; i < offset; i++, ++it) {
        if (it.IsEnd()) {
          return;
        }
      }

      // Collect results
      for (uint64_t i = 0; i < limit && !it.IsEnd(); i++, ++it) {
        result.push_back(it->second);
      }
    } else {
      // Case 2.2: full scan + backward scan

      std::queue<ValueType> result_queue;

      // Collect the first (limit + offset) nodes
      for (uint64_t i = 0; i < limit + offset && !it.IsEnd(); i++, ++it) {
        result_queue.push(it->second);
      }

      // Translate the window until it reaches the end of the list
      while (!it.IsEnd()) {
        result_queue.pop();
        result_queue.push(it->second);
        ++it;
      }

      // Dump needed result from the queue to the vector
      uint64_t result_size = MIN(limit, result_queue.size());
      for (uint64_t i = 0; i < result_size; i++) {
        result.push_back(result_queue.front());
        result_queue.pop();
      }
      std::reverse(result.begin(), result.end());
    }

  } else {
    const storage::Tuple *low_key_p = csp_p->GetLowKey();
    const storage::Tuple *high_key_p = csp_p->GetHighKey();

    LOG_TRACE("Partial scan low key: %s\n high key: %s",
              low_key_p->GetInfo().c_str(), high_key_p->GetInfo().c_str());

    KeyType index_low_key;
    KeyType index_high_key;
    index_low_key.SetFromKey(low_key_p);
    index_high_key.SetFromKey(high_key_p);

    // Find the lower bound of the search key
    auto it = container.Begin(index_low_key);

    if (scan_direction == ScanDirectionType::FORWARD) {
      // Case 3.1: range query + forward scan

      for (uint64_t i = 0; i < offset; i++, ++it) {
        if (it.IsEnd()) {
          return;
        }
      }

      // Collect results
      for (uint64_t i = 0;
           i < limit && !it.IsEnd() &&
               container.KeyCmpLessEqual(it->first, index_high_key);
           i++, ++it) {
        result.push_back(it->second);
      }
    } else {
      // Case 3.2: range query + backward scan

      std::queue<ValueType> result_queue;

      // Collect the first (limit + offset) nodes
      for (uint64_t i = 0;
           i < limit + offset && !it.IsEnd() &&
               container.KeyCmpLessEqual(it->first, index_high_key);
           i++, ++it) {
        result_queue.push(it->second);
      }

      // Translate the window until the right end of window does not satiafy the
      // query criterion
      while (!it.IsEnd() &&
             container.KeyCmpLessEqual(it->first, index_high_key)) {
        result_queue.pop();
        result_queue.push(it->second);
        ++it;
      }

      // Dump needed result from the queue to the vector
      uint64_t result_size = MIN(limit, result_queue.size());
      for (uint64_t i = 0; i < result_size; i++) {
        result.push_back(result_queue.front());
        result_queue.pop();
      }
      std::reverse(result.begin(), result.end());
    }

  }  // if is full scan
}

SKIPLIST_TEMPLATE_ARGUMENTS
void SKIPLIST_INDEX_TYPE::ScanAllKeys(std::vector<ValueType> &result) {
  auto it = container.Begin();

  // scan all entries
  while (it.IsEnd() == false) {
    result.push_back(it->second);
    ++it;
  }

  return;
}

SKIPLIST_TEMPLATE_ARGUMENTS
void SKIPLIST_INDEX_TYPE::ScanKey(const storage::Tuple *key,
                                  std::vector<ValueType> &result) {
  KeyType index_key;
  index_key.SetFromKey(key);

  // This function in SkipList fills a given vector
  container.GetValue(index_key, result);

  return;
}

SKIPLIST_TEMPLATE_ARGUMENTS
std::string SKIPLIST_INDEX_TYPE::GetTypeName() const { return "SkipList"; }

// IMPORTANT: Make sure you don't exceed CompactIntegerKey_MAX_SLOTS

template class SkipListIndex<
    CompactIntsKey<1>, ItemPointer *, CompactIntsComparator<1>,
    CompactIntsEqualityChecker<1>, ItemPointerComparator>;
template class SkipListIndex<
    CompactIntsKey<2>, ItemPointer *, CompactIntsComparator<2>,
    CompactIntsEqualityChecker<2>, ItemPointerComparator>;
template class SkipListIndex<
    CompactIntsKey<3>, ItemPointer *, CompactIntsComparator<3>,
    CompactIntsEqualityChecker<3>, ItemPointerComparator>;
template class SkipListIndex<
    CompactIntsKey<4>, ItemPointer *, CompactIntsComparator<4>,
    CompactIntsEqualityChecker<4>, ItemPointerComparator>;

// Generic key
template class SkipListIndex<GenericKey<4>, ItemPointer *,
                             FastGenericComparator<4>,
                             GenericEqualityChecker<4>, ItemPointerComparator>;
template class SkipListIndex<GenericKey<8>, ItemPointer *,
                             FastGenericComparator<8>,
                             GenericEqualityChecker<8>, ItemPointerComparator>;
template class SkipListIndex<GenericKey<16>, ItemPointer *,
                             FastGenericComparator<16>,
                             GenericEqualityChecker<16>, ItemPointerComparator>;
template class SkipListIndex<GenericKey<64>, ItemPointer *,
                             FastGenericComparator<64>,
                             GenericEqualityChecker<64>, ItemPointerComparator>;
template class SkipListIndex<
    GenericKey<256>, ItemPointer *, FastGenericComparator<256>,
    GenericEqualityChecker<256>, ItemPointerComparator>;

// Tuple key
template class SkipListIndex<TupleKey, ItemPointer *, TupleKeyComparator,
                             TupleKeyEqualityChecker, ItemPointerComparator>;

}  // namespace index
}  // namespace peloton
