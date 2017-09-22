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
#ifndef _free_explorer_hh_
#define _free_explorer_hh_

#include "op_explorer.hh"
#include "closure.hh"
#include "reachable_image.hh"

namespace ceta {
  /**
   * A triple containing three iterators that defines a range that is
   * processed by some incremental algorithm.  The range is from
   * [begin end), but there is an additional pointer to an iterator in the
   * range [begin end] that points to the first value that has not been
   * processed by the algorithm.  If begin_new equals begin, then the
   * algorithm has processed no elements so far.  If begin_new equals end,
   * then the algorithm has processed every element.
   */
  template<typename I>
  class incremental_range_t {
  public:
    typedef I iterator;

    incremental_range_t(I begin, I begin_new, I end)
      : begin_(begin),
        begin_new_(begin_new),
        end_(end) {
    };
    /** Returns iterator that points to first element in range. */
    I begin() {
      return begin_;
    }
    I begin_new() {
      return begin_new_;
    }
    I end() {
      return end_;
    }
  private:
    I begin_;
    I begin_new_;
    I end_;
  };

  /**
   * Applies F to any new combination of iterators.
   * I is a bidirectional iterator that points to an iterator range over
   * some type of iterators called the underlying iterator.
   * p is an unary predicate that accepts a vector of underlying iterators.
   * It should throw an exception if it wants to abort processing new
   * combinations.
   */
  template<typename I, typename UnaryPredicate>
  void new_combinations(I first, I last, UnaryPredicate& p) {
    // Get index of last column with unprocessed values.
    I last_new_range = last;
    for (I i = first; i != last; ++i) {
      if (i->begin_new() != i->end())
        last_new_range = i;
    }
    // If there are no ranges with new inputs, then return
    if (last_new_range == last) return;

    // Get type of iterator that incremental range is over.
    typedef typename std::iterator_traits<I>::value_type::iterator
            element_iterator;

    size_t input_count = std::distance(first, last);
    std::vector<element_iterator> inputs;
    inputs.reserve(input_count);
    for (I i = first; i != last; ++i)
      inputs.push_back(i->begin());


    typedef typename std::vector<element_iterator>::const_iterator
            element_vector_const_iter;
    typedef typename std::vector<element_iterator>::iterator
            element_vector_iter;
    // Points to last input argument.
    element_vector_const_iter last_input = inputs.end() - 1;

    // Points to last assigned input.
    element_vector_iter cur_input = inputs.begin();
    // Stores number of iterators in inputs that point to new value.
    *cur_input = (first == last_new_range)
               ? first->begin_new()
               : first->begin();
    // Stores number of assigned arguments that point to new elements.
    size_t new_count = (*cur_input == first->begin_new()) ? 1 : 0;
    // Points to last assigned range.
    I cur_range = first;
    while (inputs[0] != first->end()) {
      // If we have reached end for this argument
      if (*cur_input == cur_range->end()) {
        // Since *cur_input == cur_range->end(), we must be at a new state
        // and so new_count must be decremented.
        --new_count;
        // Goto previous level
        --cur_input;
        --cur_range;
        // Goto next input.
        ++(*cur_input);
      // If we have not yet assigned last input
      } else if (cur_input != last_input) {
        // Goto next level
        ++cur_input;
        ++cur_range;
        // Select initial input for next argument.
        *cur_input = (new_count == 0) && (cur_range == last_new_range)
                   ? cur_range->begin_new()
                   : cur_range->begin();
      // else explore current state.
      } else {
        const std::vector<element_iterator>& const_inputs = inputs;
        p(const_inputs);
        // Goto next input.
        ++(*cur_input);
      }
      // Increment new_count if we just reached new input.
      if (*cur_input == cur_range->begin_new())
        ++new_count;
    }
  }

  /**
   * Function object that returns set of states given vector pointing
   * to reachable inputs.
   */
  class next_fn_t {
    typedef std::pair<std::set<state_t>, term_t> reachable_t;
  public:
    next_fn_t(const theory_t& theory,
              const op_t& op,
              const closure_t& closure,
              const std::vector<rule_t>& rules,
              reachable_sets_t& reachables)
      : theory_(theory),
        op_(op),
        closure_(closure),
        rules_(closure.op_rules(op)),
        reachables_(reachables) {
    }

    /** Add reachable states for inputs to reachables_states_ */
    void operator()(const std::vector<reachable_image_t::iterator>& inputs) {
      std::set<state_t> states;
      typedef std::vector<rule_t>::const_iterator rule_iter;
      for (rule_iter i = rules_.begin(); i != rules_.end(); ++i) {
        if (lhs_in_inputs(*i, inputs)) {
          closure_.add_and_close(states, rhs(*i));
        }
      }
      std::vector<term_t> subterms;
      subterms.reserve(inputs.size());
      typedef std::vector<reachable_image_t::iterator>::const_iterator
              input_iter;
      for (input_iter i = inputs.begin(); i != inputs.end(); ++i) {
        subterms.push_back((*i)->second);
      }
      term_t term(theory_, op_, subterms.begin(), subterms.end());
      reachables_.add(states, term);
    }
  private:
    /**
     * Returns true if each state in the left-hand-side of the rule is in
     * the set of reachable states for the corresponding input.
     */
    bool lhs_in_inputs(const rule_t& rule,
                    const std::vector<reachable_image_t::iterator>& inputs) {
      typedef rule_t::lhs_state_iterator state_iter;
      typedef std::vector<reachable_image_t::iterator>::const_iterator
              input_iter;
      input_iter cur_input = inputs.begin();
      state_iter cur_state = lhs_states_begin(rule);
      state_iter end_state = lhs_states_end(rule);
      bool result = true;
      while (result && (cur_state != end_state)) {
        // Return false if current input set does not contain current
        // state.
        result = (*cur_input)->first.count(*cur_state) > 0;
        ++cur_state;
        ++cur_input;
      }
      return result;
    }

    const theory_t theory_;
    const op_t op_;
    const closure_t& closure_;
    const std::vector<rule_t>& rules_;
    reachable_sets_t& reachables_;
  };

  /** Reachable set explorer for a free operator. */
  class free_explorer_t : public op_explorer_t {
    typedef std::pair<std::set<state_t>, term_t> reachable_t;
  public:
    /** Constructs a new free explorer. */
    free_explorer_t(const theory_t theory,
                    const op_t& op,
                    const closure_t& closure)
      : theory_(theory),
        op_(op),
        axioms_(axioms(theory, op)),
        closure_(closure),
        rules_(closure.op_rules(op)),
        complete_(true),
        processed_counts_(input_count(op), 0) {
      op_t::input_iterator end = inputs_end(op);
      reachable_images_.reserve(input_count(op));
      for (op_t::input_iterator i = inputs_begin(op); i != end; ++i) {
        size_t cur_idx = reachable_images_.size();
        reachable_images_.push_back(reachable_image_t(
                lhs_states(rules_.begin(), rules_.end(), cur_idx)));
      }
    }

    /** Adds a reachable set to explorer. */
    void add_reachable(const std::set<state_t>& set, const term_t& term) {
      for (size_t i = 0; i != input_count(op_); ++i) {
        // Add term and set if kind matches and term is not identity.
        bool should_add = (kind(term) == input(op_, i))
                       && !is_identity(root(term), axioms_, i);
        if (should_add && reachable_images_[i].add(set, term))
          complete_ = false;
      }
    }

    void explore(reachable_sets_t& reachables) {
      typedef reachable_image_t::iterator image_iter;
      // Range for each input.
      std::vector< incremental_range_t<image_iter> > ranges;
      ranges.reserve(input_count(op_));
      // Construct each range.
      for (size_t i = 0; i != input_count(op_); ++i) {
        const reachable_image_t& image = reachable_images_[i];
        size_t old_size = processed_counts_[i];
        // Add range for input
        ranges.push_back(incremental_range_t<image_iter>(
                   image.begin(), image.begin() + old_size, image.end()));
      }
      next_fn_t fn(theory_, op_, closure_, rules_, reachables);
      // Explore all new combinations
      new_combinations(ranges.begin(), ranges.end(), fn);
      // Update processed counts
      for (size_t i = 0; i != input_count(op_); ++i) {
        const reachable_image_t& image = reachable_images_[i];
        processed_counts_[i] = state_count(image);
      }
      complete_ = true;
    }

    /** Returns true if this explorer has completely explored states. */
    bool is_complete(void) const {
      return complete_;
    }
  private:
    /** Theory for explorer. */
    const theory_t theory_;
    /** Operator for explorer. */
    const op_t op_;
    /** Axioms for operator. */
    const axiom_set_t axioms_;
    /** Epsilon closure for automaton. */
    const closure_t& closure_;
    /** Rules for operator. */
    const std::vector<rule_t> rules_;
    /**
     * The reachable states for each input intersected with the states
     * that are used by that input.
     */
    std::vector<reachable_image_t> reachable_images_;
    /** Indicates if explorer is complete. */
    bool complete_;
    /** The number of state sets in each image that have been processed. */
    std::vector<size_t> processed_counts_;
  };
}

#endif
