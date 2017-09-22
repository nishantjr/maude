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

/**
 * \file
 * Implementation for tree automata subset construction operations.
 */

#include <list>

#include "subset_construction.hh"
#include "free_explorer.hh"
#include "comm_explorer.hh"
#include "assoc_explorer.hh"
#include "semilinear_ac_explorer.hh"
#include "counter_ac_explorer.hh"
#include "lcounter_ac_explorer.hh"

//#define LCOUNTER_AC_EXPLORER

namespace ceta {
  op_explorer_t* new_explorer(const theory_t& theory,
                              const op_t& op,
                              const closure_t& closure) {
    const std::vector<rule_t>& rules = closure.op_rules(op);
    const axiom_set_t& cur_axioms = axioms(theory, op);
    if (is_assoc(cur_axioms)) {
      if (is_comm(cur_axioms)) {
#ifdef LCOUNTER_AC_EXPLORER
        return new lcounter_ac_explorer_t(theory, op, closure, rules);
#else
        return new semilinear_ac_explorer_t(theory, op, closure, rules);
#endif
      } else {
        return new assoc_explorer_t(theory, op, closure, rules);
      }
    } else {
      if (is_comm(cur_axioms)) {
        return new comm_explorer_t(theory, op, closure, rules);
      } else {
        return new free_explorer_t(theory, op, closure);
      }
    }
  }

  /** Implementation of subset constructor algorithm. */
  class subset_constructor_impl {
  public:
    /** Constructs a new subset constructor implementation. */
    subset_constructor_impl(const ta_t& ta,
                            const std::set<state_t>& pos_states,
                            const std::set<state_t>& neg_states)
      : closure_(ta),
        reachables_(ta, pos_states, neg_states, queue_) {
      const theory_t& cur_theory = theory(ta);


      typedef theory_t::op_iterator op_iter;
      op_iter end = ops_end(theory(ta));
      for (op_iter i = ops_begin(theory(ta)); i != end; ++i) {
        const op_t& op = *i;
        if (is_constant(op)) {
          // Add reachable set for each constant to reachables_
          const std::set<state_t>& rep_set = closure_.reachables(op);
          term_t term = make_constant(cur_theory, op);
          reachables_.add(rep_set, term);
        } else {
          // Generate new explorer.
          explorers_.push_back(explorer_ptr(
                  new_explorer(cur_theory, op, closure_)));
        }
      }
    }

    /** Performs some finite amount of work in subset construction. */
    void work(void) {
      if (!active_.empty()) {
        op_explorer_t& cur_explorer = *active_.front();
        cur_explorer.explore(reachables_);
        // Deactivate explorer if complete.
        if (cur_explorer.is_complete()) {
          active_.pop_front();
        }
      }
    }

    /** Returns true if subset construction has found all reachable sets. */
    bool is_complete(void) const {
      return queue_.empty() && active_.empty();
    }

    /** Returns true if constructor has a new reachable set. */
    bool has_next(void) const {
      return !queue_.empty();
    }

    /** Returns next reachable set. */
    const std::set<state_t> next_set(void) const {
      const std::set<state_t>& rep_set = queue_.front().first;
      return closure_.full_set(rep_set);
    }

    /** Returns term for next reachable set. */
    const term_t& next_term(void) const {
      return queue_.front().second;
    }

    /** Pops next reachable set from queue. */
    void pop_next(void) {
      const std::set<state_t>& set = next_set();
      const term_t& term = next_term();

      typedef explorer_list_t::iterator iter;
      for (iter i = explorers_.begin(); i != explorers_.end(); ++i) {
        boost::shared_ptr<op_explorer_t>& cur_explorer = *i;
        bool prev_complete = cur_explorer->is_complete();
        (*i)->add_reachable(set, term);
        // If i was previously complete and is not now.
        if (prev_complete && !cur_explorer->is_complete()) {
          active_.push_back(cur_explorer);
        }
      }
      queue_.pop_front();
    }
  private:
    /** Disable copy constructor. */
    subset_constructor_impl(const subset_constructor_impl&);
    /** Disable assignment. */
    subset_constructor_impl& operator=(const subset_constructor_impl&);
    typedef boost::shared_ptr<op_explorer_t> explorer_ptr;
    typedef std::pair<std::set<state_t>, term_t> reachable_t;
    typedef std::list<explorer_ptr> explorer_list_t;

    /**
     * Epsilon closure data structure.  Must be a member of class because
     * explorers may point to it.
     */
    closure_t closure_;
    /** Queue of explorers that are active. */
    std::deque<explorer_ptr> active_;
    /** List of non-constant operator explorers. */
    explorer_list_t explorers_;
    /** Queue of pairs states and terms remaining to return. */
    std::deque<reachable_t> queue_;
    /** Reachable sets explored so far. */
    reachable_sets_t reachables_;
  };

  subset_constructor_t::subset_constructor_t(const ta_t& ta)
    : impl_(new subset_constructor_impl(ta,
            std::set<state_t>(states_begin(ta), states_end(ta)),
            std::set<state_t>(states_begin(ta), states_end(ta)))) {
  }

  subset_constructor_t::subset_constructor_t(const ta_t& ta,
      const std::set<state_t>& pos_states,
      const std::set<state_t>& neg_states)
    : impl_(new subset_constructor_impl(ta, pos_states, neg_states)) {
  }

  void subset_constructor_t::work(void) {
    impl_->work();
  }

  bool subset_constructor_t::is_complete(void) const {
    return impl_->is_complete();
  }

  bool subset_constructor_t::has_next(void) const {
    return impl_->has_next();
  }

  const std::set<state_t> subset_constructor_t::next_set(void) const {
    return impl_->next_set();
  }

  const term_t& subset_constructor_t::next_term(void) const {
    return impl_->next_term();
  }

  void subset_constructor_t::pop_next(void) {
    return impl_->pop_next();
  }

  /**
   * Visits elements of state predicate.  If is_pos is true, then any
   * state encountered is added to pos_states.  Otherwise, the any state
   * encountered is added to neg_states.
   */
  class sign_predicate_visitor_t {
  public:
    typedef void result_type;

    sign_predicate_visitor_t(std::set<state_t>& pos_states,
                             std::set<state_t>& neg_states)
      : pos_states_(pos_states),
        neg_states_(neg_states) {
    }


    void operator()(const bool value) {
      // Do nothing
    }

    void operator()(const state_t& state) {
      pos_states_.insert(state);
    }

    void operator()(const not_predicate_t& pred) {
      /** Reverse positive and negative. */
      sign_predicate_visitor_t v(neg_states_, pos_states_);
      apply_visitor(v, pred.arg);
    }

    void operator()(const and_predicate_t& pred) {
      apply_visitor(*this, pred.lhs);
      apply_visitor(*this, pred.rhs);
    }

    void operator()(const or_predicate_t& pred) {
      apply_visitor(*this, pred.lhs);
      apply_visitor(*this, pred.rhs);
     }
  private:
    std::set<state_t>& pos_states_;
    std::set<state_t>& neg_states_;
  };

  const test_result_t test_emptiness(const ta_t& ta) {
    // Build positive and negative states from formula.
    std::set<state_t> pos_states;
    std::set<state_t> neg_states;
    sign_predicate_visitor_t v(pos_states, neg_states);
    {
      typedef theory_t::kind_iterator iter;
      iter ibegin = kinds_begin(theory(ta));
      iter iend = kinds_end(theory(ta));
      for (iter i = ibegin; i != iend; ++i) {
        apply_visitor(v, predicate(ta, *i));
      }
    }

    subset_constructor_t sc(ta, pos_states, neg_states);
    while (!sc.is_complete()) {
      sc.work();
      while (sc.has_next()) {
        const std::set<state_t> set = sc.next_set();
        const term_t& term = sc.next_term();
        if (models(predicate(ta, kind(term)), set))
          return test_result_t(term, set);
        sc.pop_next();
      }
    }
    test_result_t accept_result;
    return accept_result;
  }

}
