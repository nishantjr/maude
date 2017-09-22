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
#ifndef _comm_explorer_hh_
#define _comm_explorer_hh_

#include "op_explorer.hh"
#include "closure.hh"
#include "reachable_image.hh"

namespace ceta {
  /** Reachable set explorer for a commutative operator. */
  class comm_explorer_t : public op_explorer_t {
    typedef std::pair<std::set<state_t>, term_t> reachable_t;
  public:
    comm_explorer_t(const theory_t& theory,
                    const op_t& op,
                    const closure_t& closure,
                    const std::vector<rule_t>& rules)
      : theory_(theory),
        op_(op),
        axioms_(axioms(theory, op)),
        closure_(closure),
        rules_(rules),
        image_(lhs_states(rules.begin(), rules.end())),
        processed_count_(0) {
    }

    void add_reachable(const std::set<state_t>& set,
                       const term_t& term) {
      // Add term and set if kind matches and term is not identity.
      if ((kind(term) == output(op_) ) && !is_identity(root(term), axioms_))
        image_.add(set, term);
    }

    void explore(reachable_sets_t& reachables) {
      typedef reachable_image_t::iterator image_iter;
      kind_t k = output(op_);
      // Explore all new combinations
      image_iter img_begin     = image_.begin();
      image_iter img_new_begin = image_.begin() + processed_count_;
      image_iter img_end       = image_.end();
      // For each new state in image
      for (image_iter i = img_new_begin; i != img_end; ++i) {
        // For every state added before i.
        for (image_iter j = img_begin; j != i + 1; ++j) {
          explore(reachables, *i, *j);
        }
      }
      // Update processed counts
      processed_count_ = state_count(image_);
    }

    /** Returns true if this explorer has completely explored states. */
    virtual bool is_complete(void) const {
      return (processed_count_ == state_count(image_));
    }
  private:
    /** Add reachable pair from x and y to reachable states. */
    void explore(reachable_sets_t& reachables,
                 const reachable_t& x, const reachable_t& y) {
      std::set<state_t> states;
      typedef std::vector<rule_t>::const_iterator rule_iter;
      for (rule_iter i = rules_.begin(); i != rules_.end(); ++i) {
        if (lhs_in_inputs(*i, x.first, y.first)) {
          closure_.add_and_close(states, rhs(*i));
        }
      }
      const term_t subterms[] = { x.second, y.second };
      term_t term(theory_, op_, subterms, subterms + 2);
      reachables.add(states, term);
    }

    /**
     * Returns true if the states in the left-hand side of the rule
     * belongs to the set of reachable states in the inputs or can
     * be permuted to do so.
     */
    bool lhs_in_inputs(const rule_t& rule, const std::set<state_t>& x,
                       const std::set<state_t>& y) {
      const state_t& lhs0 = lhs_state(rule, 0);
      const state_t& lhs1 = lhs_state(rule, 1);
      return (x.count(lhs0) > 0) && (y.count(lhs1) > 0)
          || (x.count(lhs1) > 0) && (y.count(lhs0) > 0);
    }

    /** Theory for exploer. */
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
     * The reachable states intersected with the states that appear on
     * the left-hand-side of rule for operator.
     */
    reachable_image_t image_;
    /** Number of state sets in image_ that we have explored. */
    size_t processed_count_;
  };
}

#endif
