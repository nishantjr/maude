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

#include "semilinear_ac_explorer.hh"
#include "parikh.hh"
#include "reachable_image.hh"

namespace ceta {
  /**
   * Reachable set explorer for an associative and commutative operator.
   */
  class semilinear_ac_impl_t {
  public:
    /** Constructs a new AC explorer. */
    semilinear_ac_impl_t(const theory_t& theory,
                         const op_t& op,
                         const closure_t& closure,
                         const std::vector<rule_t>& rules)
      : theory_(theory),
        op_(op),
        axioms_(axioms(theory, op)),
        closure_(closure),
        complete_(true),
        image_(lhs_states(rules.begin(), rules.end())),
        processed_count_(0),
        rhs_states_(rhs_states(rules.begin(), rules.end())) {

      std::set<state_t> states = image_.states();
      states.insert(rhs_states_.begin(), rhs_states_.end());

      // Add epsilon rules to rules_
      { typedef std::set<state_t>::const_iterator iter;
        for (iter i = states.begin(); i != states.end(); ++i) {
          const std::set<state_t>& out_edges = closure.out_edges(*i);
          for (iter j = out_edges.begin(); j != out_edges.end(); ++j) {
            grammar_.add(*j, *i);
          }
        }
      }

      // Add regular rules to grammar.
      typedef std::vector<rule_t>::const_iterator rule_iter;
      for (rule_iter i = rules.begin(); i != rules.end(); ++i) {
        // Add *i to grammar
        grammar_.add(cfg::make_rrule(
                rhs(*i), lhs_state(*i, 0), lhs_state(*i, 1)));
      }
    }

    void add_reachable(const std::set<state_t>& set, const term_t& term) {
      if ((kind(term) == output(op_))
              && (root(term) != op_)
              && !is_identity(root(term), axioms_)) {
        image_.add(set, term);
      }
    }

    /**
     * Explore new reachable states.  Note that if this operation throws
     * an exception, the explorer will become unusable.
     * TODO: Adding guiding to exploration so that:
     * * We do not explore routes that are guaranteed to reach states we
     *   already know are reachable.
     * * The exploration route will hit at least one semilinear set that
     *   is larger than it was in a previous round.
     * * Intelligently chose ordering of variables to assign.
     */
    void explore(reachable_sets_t& reachables) {
      kind_t k = output(op_);
      // Add new states in image to grammar.
      typedef reachable_image_t::iterator image_iter;
      image_iter img_begin = image_.begin() + processed_count_;
      image_iter img_end   = image_.end();
      for (image_iter i = img_begin; i != img_end; ++i) {
        grammar_.add_terminal(processed_count_);
        // Add production for each state in cur_set to cur_set to grammar.
        const std::set<state_t>& cur_set = i->first;
        typedef std::set<state_t>::const_iterator state_iter;
        state_iter set_end = cur_set.end();
        for (state_iter j = cur_set.begin(); j != set_end; ++j)
          grammar_.add(cfg::make_trule(*j, processed_count_));
        ++processed_count_;
      }

      // Get parikh image of grammar.
      typedef std::map<state_t, semilinear_set> pimage_t;
      pimage_t pimage = parikh_image(processed_count_, grammar_);

      // Initialize positive and negative semilinear sets for elements on
      // rhs.
      std::vector<semilinear_set> pos;
      pos.reserve(rhs_states_.size());
      std::vector<semilinear_set> neg;
      neg.reserve(rhs_states_.size());
      {
        typedef std::set<state_t>::const_iterator state_iter;
        state_iter end = rhs_states_.end();
        for (state_iter i = rhs_states_.begin(); i != end; ++i) {
          pos.push_back(pimage.find(*i)->second);
          neg.push_back(complement(pos.back()));
        }
      }

      size_t reachable_count = state_count(image_);
      if (reachable_count == 0)
        return;
      // Try all combinations of rhs states
      // stack maintains the semilinear set for each state offset by 1.
      std::vector<semilinear_set> stack;
      stack.reserve(rhs_states_.size() + 1);
      stack.push_back(min_size_set(reachable_count, 2));

      bool abort = false;
      std::set<state_t> states;
      // We maintain the invariants:
      // * stack.back().is_empty() == false
      std::set<state_t>::const_iterator cur_state = rhs_states_.begin();
      std::vector<semilinear_set>::const_iterator cur_pos = pos.begin();
      std::vector<semilinear_set>::const_iterator cur_neg = neg.begin();

      while (!abort) {
        // If we have assigned all states
        if (cur_state == rhs_states_.end()) {
          // Create term
          std::vector<term_t> subterms;
          {
            if (ceta::is_empty(stack.back()))
              throw std::logic_error("Stack is empty");

            const linear_set_group& g = *stack.back().begin();
            const std::vector<unsigned>& constant = *g.constants().begin();

            for (size_t i = 0; i != constant.size(); ++i) {
              const term_t& subterm = (image_.begin() + i)->second;
              subterms.reserve(subterms.size() + constant[i]);
              for (size_t c = 0; c != constant[i]; ++c)
                subterms.push_back(subterm);
            }
          }
          // Close states with respect to epsilon transitions.
          std::set<state_t> closed_states;
          closure_.add_and_close_all(closed_states,
                  states.begin(), states.end());
          term_t term(theory_, op_, subterms.begin(), subterms.end());
          reachables.add(closed_states, term);

          // Increment and backtrack to next valid state
          bool backtracking = !abort;
          while ((cur_state != rhs_states_.begin()) && backtracking) {
            stack.pop_back();
            --cur_state;
            --cur_pos;
            --cur_neg;
            if (states.count(*cur_state) > 0) {
              states.erase(*cur_state);
              semilinear_set next = intersect(stack.back(), *cur_neg);
              if (!is_empty(next)) {
                backtracking = false;
                stack.push_back(next);
                ++cur_state;
                ++cur_pos;
                ++cur_neg;
              }
            }
          }
          // If backtracking is still true, we are done
          if (backtracking)
            abort = true;
        } else {
          semilinear_set next = intersect(stack.back(), *cur_pos);
          if (!ceta::is_empty(next)) {
            // Branch to true case
            states.insert(*cur_state);
            stack.push_back(next);
          } else {
            // branch to false case
            stack.push_back(intersect(stack.back(), *cur_neg));
          }
          ++cur_state;
          ++cur_pos;
          ++cur_neg;
        }
      }
      complete_ = true;
    }

    /** Returns true if this explorer has completely explored states. */
    bool is_complete(void) const {
      return (processed_count_ == state_count(image_));
    }
  private:
    typedef std::pair<term_t, std::set<state_t> > reachable_t;

    /** Theory we are operating in. */
    const theory_t theory_;
    /** Operator for explorer. */
    const op_t op_;
    /** Axioms for operator. */
    const axiom_set_t axioms_;
    /** Epsilon closure for automaton. */
    const closure_t& closure_;
    /** Context free grammar built for rules of AC_explorer. */
    cfg::cfg_t<size_t, state_t> grammar_;
    /** Indicates if explorer is complete. */
    bool complete_;
    /**
     * The reachable states intersected with the states that appear on
     * the left-hand-side of rule for operator.
     */
    reachable_image_t image_;
    /** Number of state sets in image_ that have been processed. */
    size_t processed_count_;
    /** States that appear on rhs of rule for op. */
    std::set<state_t> rhs_states_;
  };

  semilinear_ac_explorer_t::semilinear_ac_explorer_t(const theory_t& theory,
          const op_t& op,
          const closure_t& closure,
          const std::vector<rule_t>& rules)
    : impl_(new semilinear_ac_impl_t(theory, op, closure, rules)) {
  }

  void semilinear_ac_explorer_t::add_reachable(
          const std::set<state_t>& states, const term_t& term) {
    impl_->add_reachable(states, term);
  }

  void semilinear_ac_explorer_t::explore(reachable_sets_t& reachables) {
    impl_->explore(reachables);
  }

  bool semilinear_ac_explorer_t::is_complete(void) const {
    return impl_->is_complete();
  }
}
