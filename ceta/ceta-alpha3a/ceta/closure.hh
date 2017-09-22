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
#ifndef _closure_hh_
#define _closure_hh_
/** \file
 * \brief Data structure for computing transitive closure of epsilon rules
 * including epsilon rules induced by identities applied to regular rules.
 */

#include <queue>
#include <utility>

#include "bi_graph.hh"

namespace ceta {
  namespace closure {
    /**
     * Computes epsilon closure relation in automaton from epsilon
     * transitions and transitions potentially involving identity elements.
     */
    template<typename Constant, typename State>
    class epsilon_closure_t {
    public:
      /** Constructs an epsilon transition graph with no transitions. */
      epsilon_closure_t() {
      }

      /** Returns set of states reachable from state. */
      const std::set<State>& reachables(const State& lhs) const {
        add_self_loop(lhs);
        process_pending();
        return erules_.children(lhs);
      }

      /** Returns set of states reachable from constant.  */
      const std::set<State>& reachables(const Constant& op) const {
        process_pending();
        return idrules_.children(op);
      }

      /** Adds transition from lhs -> rhs. */
      void add_erule(const State& lhs, const State& rhs) {
        add_self_loop(lhs);
        add_self_loop(rhs);
        // Make sure erules contains self inverse for lhs and rhs.
        if (!is_reachable(lhs, rhs))
          pending_.push(erule_t(lhs, rhs));
      }

      /** Adds a transition from lhs -> rhs. */
      void add_rule(const Constant& lhs, const State& rhs) {
        add_self_loop(rhs);
        if (!is_reachable(lhs, rhs))
          private_add(lhs, rhs);
      }

      /**
       * Adds a guarded transition where if op ->* target, then
       * lhs -> rhs.
       */
      void add_guarded(const Constant& op, const State& target,
                       const State& lhs, const State& rhs) {
        if (is_reachable(op, target)) {
          add_erule(lhs, rhs);
        } else {
          watched_rules_[idrule_t(op, target)].insert(erule_t(lhs, rhs));
        }
      }

      /** Returns true if rhs of rule is reachable from lhs of rule. */
      template<typename Lhs, typename Rhs>
      bool is_reachable(const Lhs& lhs, const Rhs& rhs) const {
        return reachables(lhs).count(rhs) > 0;
      }
    private:
      typedef std::pair<State, State> erule_t;
      typedef std::pair<Constant, State> idrule_t;

      /** Sets self loop for state in idrules. */
      void add_self_loop(const State& state) const {
        erules_.insert(state, state);
      }

      /** Adds lhs -> rhs to list of idrules and discover new erules. */
      void private_add(const Constant& lhs, const State& rhs) const {
        if (idrules_.contains(lhs, rhs))
          return;
        add_self_loop(rhs);

        size_t count = 0;
        try {
          // Add each watched rule guarded by this rule to pending.
          std::set<erule_t>& erules = watched_rules_[idrule_t(lhs, rhs)];
          typedef typename std::set<erule_t>::const_iterator erule_iter;
          erule_iter end = erules.end();
          for (erule_iter i = erules.begin(); i != end; ++i) {
            pending_.push(*i);
            ++count;
          }
          // Add transition (may throw)
          const std::set<State>& rhsc = erules_.children(rhs);
          typedef typename std::set<State>::const_iterator state_iter;
          for (state_iter i = rhsc.begin(); i != rhsc.end(); ++i)
            idrules_.insert(lhs, *i);
          erules.clear();
        } catch (...) {
          while (count > 0) {
            pending_.pop();
            --count;
          }
          throw;
        }
      }

      /** Process pending updates. */
      void process_pending() const {
        while (!pending_.empty()) {
          const State top_lhs = pending_.front().first;
          const State top_rhs = pending_.front().second;
          typedef typename std::set<State>::const_iterator set_iter;

          const std::set<State>& rhsc = erules_.children(top_rhs);
          set_iter rhsc_end = rhsc.end();

          // Add state -> state transititions
          const std::set<State>& lhsp = erules_.parents(top_lhs);
          set_iter lhsp_end = lhsp.end();
          for (set_iter iorg = lhsp.begin(); iorg != lhsp_end; ++iorg) {
            if (erules_.contains(*iorg, top_rhs))
              continue;
            for (set_iter idst = rhsc.begin(); idst != rhsc_end; ++idst) {
              if (*idst != top_rhs) {
                erules_.insert(*iorg, *idst);
              }
            }
            erules_.insert(*iorg, top_rhs);
          }

          // Add op -> state transitions that use top pending rule.
          typedef typename std::set<Constant>::const_iterator op_iter;
          const std::set<Constant>& lhsops = idrules_.parents(top_lhs);
          op_iter lhsops_end = lhsops.end();
          for (op_iter iop = lhsops.begin(); iop != lhsops_end; ++iop) {
            if (idrules_.contains(*iop, top_rhs))
              continue;
            for (set_iter idst = rhsc.begin(); idst != rhsc_end; ++idst) {
              // Add *iop -> *idst (may throw)
              if (*idst != top_rhs)
                private_add(*iop, *idst);
            }
            private_add(*iop, top_rhs);
          }
          pending_.pop();
        }
      }
      // erules_ and idrules_ contains the epsilon closure of the current
      // graph.  We maintain the invariant that the transition graph stored
      // in these is a superset of the epsilon closure of the rules added to
      // this closure that are not in pending, and a subset of the rules in
      // pending.

      /** Bidirectional graph for the epsilon rules in the automaton. */
      mutable bi_graph_t<State, State> erules_;
      /**
       * Bidirectional graph for the constant -> state rules in the
       * automaton.  Note that we really don't need the bidirectional
       * capabilities here.  We could make do with a map that merely
       * mapped states to the identies that can reach them.
       */
      mutable bi_graph_t<Constant, State> idrules_;
      /**
       * Mapping from identity -> state rules to the set of epsilon rules
       * that they guard.  We maintain the invariant that if
       * idrules_.contains(id, state) is true then there are no guarded
       * rules for id -> state.
       */
      mutable std::map<idrule_t, std::set<erule_t> > watched_rules_;
      /**
       * Pending epsilon rules that have been added but for which the
       * epsilon closure has not been completely computed.
       */
      mutable std::queue<erule_t> pending_;
    };

    /**
     * Returns the set obtained by unioning the reachable states for
     * every element in the range.
     */
    template<typename StateIterator, typename Constant, typename State>
    inline
    const std::set<State>
    closed_set(const epsilon_closure_t<Constant, State>& closure,
               StateIterator first, StateIterator last) {
      std::set<State> result;
      for (StateIterator i = first; i != last; ++i) {
        if (result.count(*i) == 0) {
          const std::set<State>& cur_set = closure.reachables(*i);
          result.insert(cur_set.begin(), cur_set.end());
        }
      }
      return result;
    }
  }
}
#endif
