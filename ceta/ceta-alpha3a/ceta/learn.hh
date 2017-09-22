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


template<typename LeafLabel, typename BranchLabel>
class decision_tree_t {
public:
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


/**
 * A classification tree or distinguishing states in the dfa during
 * learning.  This class uses a binary membership function that should take
 * two vectors of symbols and return true if the string formed by
 * concatenating the vectors is in the language.
 * State represents a state in a deterministic automaton execution whose
 * only observable characteristic is a boolean acceptance value and who reads
 * in a character at each step.  It must be copy constructable and implement
 * the following methods:
 * - accept() -- Returns true if this is an accepting state.
 * - advance(const Alphabet& char) -- advances state to next state following
 *   the read of the given character.
 */
template<typename Alphabet, typename State>
class classifier_t {
  typedef boost::shared_ptr<State> shared_state_ptr;
public:
  /**
   * Construct a new classifier for a machine with the given initial state.
   */
  classifier_t(const State& initial)
    : tree_(shared_state_ptr(new State(initial))) {
  }

  /** Returns a pointer to the initial state in the classifier. */
  const State* initial(void) const {
    return tree_.leaf_label(tree_.initial()).get();
  }

  /**
   * Returns a pointer to the representative state corresponding to the
   * given state in this classifier.
   */
  const State* classify(const State& state_arg) const {
    size_t rep = tree_.find_rep(state_pred_t(state_arg));
    return tree_.leaf_label(rep).get();
  }

  /**
   * Analyzes the trace to discover new distiguishable states that the
   * classifier does not already know about.  The trace iterators enumerate
   * an Alphabet String.  The StateIterator enumerates the state string
   * along that path.  The first state corresponds to the initial state and
   * the ith following state corresponds to the state after reading i values
   * from the trace.
   *
   * TODO: We may want to assume that this is a counterexample string, and
   * use a binary search to find a state where we disagree.  This is part of
   * the Rivest-Schapire binary search method.
   */
  template<typename StateIterator, typename TraceIterator>
  void analyze(StateIterator state_begin, StateIterator state_end,
               TraceIterator trace_begin) {
    // If there is only zero or one states, then we can learn nothing
    if (std::distance(state_begin, state_end) <= 1)
      return;

    // If root is a leaf, then there must just be one state -- the initial
    // state.
    if (tree_.is_leaf(0)) {
      bool accept = tree_.leaf_label(0)->accept();
      // Iterate through trace until we find a character whose
      // acceptance does not equal accept
      StateIterator istate = state_begin;
      while ((istate != state_end) && (istate->accept() == accept)) {
        ++istate;
      }
      // If we find a difference
      if (istate->accept() != accept) {
        // Make new parent branch for root and set new root to it.
        insert_parent_branch(0, cons_list_t<Alphabet>(), accept, *istate);
      }
    } else {
      // State of the target automaton as it executes along trace.
      StateIterator istate = state_begin;
      // Representative of current state.
      size_t cur_rep = tree_.find_rep(state_pred_t(*istate));
      // Pointer to previous state representative.
      size_t prev_rep;
      // Next input istate will read.
      TraceIterator itrace = trace_begin;
      // Stores representative of advancing previous representive of *istate
      // by pending character.
      size_t lookup_rep;
      // Go to future state.
      ++istate;
      do {
        // Get next lookup rep.
        State next_state = *tree_.leaf_label(cur_rep);
        next_state.advance(*itrace);
        lookup_rep = tree_.find_rep(state_pred_t(next_state));
        // Go to future input
        ++itrace;
        // Save current rep.
        prev_rep = cur_rep;
        // Catch up to istate
        cur_rep = tree_.find_rep(state_pred_t(*istate));
        // Go to future state.
        ++istate;
      } while ((lookup_rep == cur_rep) && (istate != state_end));
      // If nodes are different
      if (cur_rep != lookup_rep) {
        // Backup to state and input that lead to differences.
        --istate;
        --itrace;

        // Get highest ancestor of lookup_rep that is not an ancestor of
        // cur_rep.
        size_t lookup_ancestor = highest_difference(lookup_rep, cur_rep);

        // Get lowest common ancestor.
        size_t lowest_common = tree_.parent(lookup_ancestor);

        // Determine whether lookup representative was along accepting path
        // with distinguisher.
        bool lookup_accept =
              tree_.accept_child(lowest_common) == lookup_ancestor;

        // Backup to state with common representative.
        --istate;
        // Create new distinguisher.
        cons_list_t<Alphabet>
                new_d(*itrace, tree_.branch_label(lowest_common));
        // Insert new parent branch for prev_rep.
        insert_parent_branch(prev_rep, new_d, lookup_accept, *istate);
      }
    }
    // TODO: As an optimization, do backwards analysis to determine if
    // newly learned difference implies additional differences.
  }
private:
  /**
   * A state predicate provides a unary function that accepts or rejects
   * cons lists based on whether a state accepts them after advancing through
   * the string elements.
   */
  class state_pred_t {
  public:
    /** Construct a predicate for the given state. */
    state_pred_t(const State& state)
      : state_(state) {
    }

    /** Returns true if state_ accepts after advancing through list. */
    bool operator()(const cons_list_t<Alphabet>& list) const {
      // If this branch has the empty string as a distinguisher
      if (list.empty()) {
        return state_.accept();
      } else {
        cons_list_t<Alphabet> l = list;
        State state_copy = state_;
        while (!l.empty()) {
          state_copy.advance(l.first());
          l = l.rest();
        }
        return state_copy.accept();
      }
    }
  private:
    const State state_;
  };

  /** Type of path to a node's root. */
  typedef std::vector<size_t> path_t;

  /**
   * Returns pointer to highest ancestor in x's path that does not occur in
   * y's path.
   */
  size_t highest_difference(size_t x, size_t y) {
    // Get path to x and y.
    path_t x_path = tree_.path(x);
    path_t y_path = tree_.path(y);

    // Iterate in reverse order (oldest first) until we find first
    // difference.
    typedef typename path_t::const_reverse_iterator path_iter;
    path_iter ix = x_path.rbegin();
    path_iter iy = y_path.rbegin();
    while (*ix == *iy) {
      ++ix;
      ++iy;
    }
    return *ix;
  }

  /** Constructs a new branch as a parent to insert_point. */
  void insert_parent_branch(size_t insert_point,
                            const cons_list_t<Alphabet>& d,
                            bool insert_point_accepts,
                            const State& new_state) {
    tree_.make_branch(insert_point, d, insert_point_accepts,
                      shared_state_ptr(new State(new_state)));
  }
  /** Classification tree. */
  decision_tree_t<shared_state_ptr, cons_list_t<Alphabet> > tree_;
};

}}
#endif
