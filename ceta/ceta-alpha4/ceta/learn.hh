/* Copyright 2006 University of Illinois at Urbana-Champaign
 *
 * Ceta is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 */
#ifndef _learn_hh_
#define _learn_hh_

#include <map>
#include <ostream>
#include <stdexcept>
#include <utility>
#include <vector>

#include <boost/shared_ptr.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/variant.hpp>
#include <boost/weak_ptr.hpp>

#include <iostream>
using namespace std;

namespace ceta {
namespace fa {

/** A reference-counted acyclic Lisp-like cons cell list. */
template<typename Alphabet>
class cons_list_t {
public:
  /** Construct an empty const list. */
  cons_list_t(void) {
  }
  /** Construct a new nonempty cons list. */
  cons_list_t(const Alphabet& first_arg,
              const cons_list_t& rest_arg)
    : impl_(new impl_t(first_arg, rest_arg)) {
  }

  /** Returns true if this represents the empty string. */
  bool empty(void) const {
    return impl_ == NULL;
  }

  /** Returns first character of list if it is nonempty. */
  const Alphabet& first(void) const {
    return impl_->first;
  }

  /** Returns rest of list if it is nonempty. */
  const cons_list_t& rest(void) const {
    return impl_->second;
  }
private:
  /** Type of implementation for nonempty cons list. */
  typedef std::pair<Alphabet, cons_list_t<Alphabet> > impl_t;
  /** Pointer to implementation. */
  boost::shared_ptr<impl_t> impl_;
};

/** Writes list to output stream. */
template<typename Alphabet>
std::ostream& operator<<(std::ostream& o,
                         const cons_list_t<Alphabet>& list) {
  cons_list_t<Alphabet> l = list;
  while (!l.empty()) {
    o << l.first();
    l = l.rest();
  }
  return o;
}

/**
 * A non-empty binary tree with labeled leafs and branches designed to
 * classify elements with the same type as the leaf level.
 */
template<typename LeafLabel, typename BranchLabel>
class decision_tree_t {
public:
  /** Creates a tree with a single root leaf. */
  decision_tree_t(const LeafLabel& initial)
    : nodes_(1, node_t(0, initial)),
      initial_(0) {
  }

  /** Returns total size of tree. */
  size_t size(void) const {
    return nodes_.size();
  }

  /** Returns index of inital leaf that was added. */
  size_t initial(void) const {
    return initial_;
  }

  /** Returns parent of node. */
  size_t parent(size_t node) const {
    if (!in_range(node)) throw std::logic_error("Index is not a node.");
    return nodes_[node].parent;
  }

  /** Return true if this node is a leaf. */
  bool is_leaf(size_t node) const {
    if (!in_range(node)) throw std::logic_error("Index is not a node.");
    return boost::get<leaf_t>(&(nodes_[node].data)) != NULL;
  }

  /** Returns label on a leaf. */
  const LeafLabel& leaf_label(size_t leaf) const {
    if (!in_range(leaf)) throw std::logic_error("Index is not a node.");
    if (!is_leaf(leaf)) throw std::logic_error("Node is not a leaf.");
    return boost::get<leaf_t>(nodes_[leaf].data).label;
  }

  /** Returns label on a branch. */
  const BranchLabel& branch_label(size_t branch) const {
    if (!in_range(branch)) throw std::logic_error("Index is not a node.");
    if (is_leaf(branch)) throw std::logic_error("Node is not a branch.");
    return boost::get<branch_t>(nodes_[branch].data).label;
  }

  /** Returns accepting child of branch. */
  size_t accept_child(size_t branch) const {
    if (!in_range(branch)) throw std::logic_error("Index is not a node.");
    if (is_leaf(branch)) throw std::logic_error("Node is not a branch.");
    return boost::get<branch_t>(nodes_[branch].data).child;
  }

  /** Returns rejecting child of branch. */
  size_t reject_child(size_t branch) const {
    return accept_child(branch) + 1;
  }

  /**
   * Converts leaf node into a branch with given label.
   * The existing leaf node is made either the accepting or rejecting child
   * depending on whether cur_leaf_accepts is true.  The other child is
   * labeled with new_leaf.
   */
  void make_branch(size_t cur_leaf,
                   const BranchLabel& branch_label,
                   bool cur_leaf_accepts,
                   const LeafLabel& new_leaf) {
    if (!is_leaf(cur_leaf)) {
      *static_cast<int*>(0) = 2;
    }
    if (!in_range(cur_leaf)) throw std::logic_error("Index is not a node.");
    if (!is_leaf(cur_leaf)) throw std::logic_error("Node is not a leaf.");
    size_t  cur_size = nodes_.size();
    nodes_.reserve(cur_size + 2);
    if (cur_leaf_accepts) {
      nodes_.push_back(node_t(cur_leaf, leaf_label(cur_leaf)));
      nodes_.push_back(node_t(cur_leaf, new_leaf));
      // Update initial if it is moving.
      if (cur_leaf == initial_)
        initial_ = cur_size;
    } else {
      nodes_.push_back(node_t(cur_leaf, new_leaf));
      nodes_.push_back(node_t(cur_leaf, leaf_label(cur_leaf)));
      // Update initial if it is moving.
      if (cur_leaf == initial_)
        initial_ = cur_size + 1;
    }
    nodes_[cur_leaf].data = branch_t(branch_label, cur_size);
  }

  /** Returns path starting from this node and ending with the root. */
  const std::vector<size_t> path(size_t node) const {
    std::vector<size_t> result;
    while (node != 0) {
      result.push_back(node);
      node = parent(node);
    }
    result.push_back(0);
    return result;
  }

  /**
   * Returns leaf node based on how predicate answers each distinguisher
   * query.
   */
  template<typename Predicate>
  size_t find_rep(const Predicate& pred, size_t node = 0) const {
    // While node is a branch
    while (!is_leaf(node)) {
      // Choose accept or reject child.
      node = pred(branch_label(node))
           ? accept_child(node)
           : reject_child(node);
    }
    // Return current node.
    return node;
  }
private:
  /** Returns true if node is in the valid range. */
  bool in_range(size_t node) const {
    return (0 <= node) && (node < nodes_.size());
  }

  /** Data for a branch node. */
  struct branch_t {
    branch_t(const BranchLabel& label_arg, size_t child_arg)
      : label(label_arg),
        child(child_arg) {
    }
    BranchLabel label;
    size_t child;
  };

  /** Data for leaf node. */
  struct leaf_t {
    leaf_t(const LeafLabel& label_arg)
      : label(label_arg) {
    }
    LeafLabel label;
  };

  /** Private data structure for storing nodes. */
  struct node_t {
    /** Construct a leaf node. */
    node_t(size_t parent_arg, const LeafLabel& label)
      : parent(parent_arg),
        data(leaf_t(label)) {
    }
    size_t parent;
    boost::variant<branch_t, leaf_t> data;
  };
  /** Vector of nodes in tree. */
  std::vector<node_t> nodes_;
  /** Index of initial leaf node. */
  size_t initial_;
};

}}
#endif
