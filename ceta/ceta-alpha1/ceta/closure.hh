/* Copyright 2005 Joe Hendrix
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
#include <queue>
#include <utility>

#include "bi_graph.hh"
#include "ceta.hh"
#include <iostream>

using namespace std;

namespace ceta {
  namespace closure {
ostream& operator<<(ostream& o, const set<state_t>& s) {
  o << "{";
  typedef set<state_t>::const_iterator set_iter;
  set_iter i = s.begin();
  set_iter end = s.end();
  if (i != end) {
    o << *i;
    ++i;
    while (i != end) {
      o << ", " << *i;
      ++i;
    }
  }
  o << "}";
  return o;
}

    typedef std::pair<op_t, state_t> idrule_t;

    static inline
    op_t lhs(const idrule_t& rule) {
      return rule.first;
    }
    
    static inline
    state_t rhs(const idrule_t& rule) {
      return rule.second;
    }

    /**
     * Computes epsilon closure relation in automaton from epsilon
     * transitions and transitions potentially involving identity elements.
     */
    class epsilon_closure_t {
    public:
      /** Constructs an epsilon transition graph with no transitions. */
      epsilon_closure_t() {
      }
    private:
      friend const std::set<state_t>&
            reachables(const epsilon_closure_t& closure, const state_t& lhs);
      friend const std::set<state_t>&
            reachables(const epsilon_closure_t& closure, const op_t& op);
      friend void add(epsilon_closure_t& closure, const erule_t& erule);
      friend void add(epsilon_closure_t& closure, const idrule_t& rule);
      friend void add_guarded(epsilon_closure_t& closure,
                              const idrule_t& guard, const erule_t& erule);

      /** Sets self loop for state in idrules. */
      void add_self_loop(const state_t& state) const {
        erules_.insert(state, state);
      }

      /** Adds rule to list of idrules and discover new erules. */
      void private_add(const idrule_t& rule) const {
        if (idrules_.contains(lhs(rule), rhs(rule)))
          return;

        size_t count = 0;
        try {
          // Add each watched rule guarded by this rule to pending.
          std::set<erule_t>& erules = watched_rules_[rule];
          typedef std::set<erule_t>::const_iterator erule_iter;
          erule_iter end = erules.end();
          for (erule_iter i = erules.begin(); i != end; ++i) {
            pending_.push(*i);
            ++count;
          }
          // Add transition (may throw)
          const std::set<state_t>& rhsc = erules_.children(rhs(rule));
          typedef std::set<state_t>::const_iterator state_iter;
          for (state_iter i = rhsc.begin(); i != rhsc.end(); ++i)
            idrules_.insert(lhs(rule), *i);
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
          const state_t top_lhs = lhs(pending_.front());
          const state_t top_rhs = rhs(pending_.front());
          typedef std::set<state_t>::const_iterator set_iter;

          //cerr << "pending " << top_lhs << " -> " << top_rhs << endl;
 
          const std::set<state_t>& rhsc = erules_.children(top_rhs);
          set_iter rhsc_end = rhsc.end(); 

          // Add state -> state transititions 
          const std::set<state_t>& lhsp = erules_.parents(top_lhs);
          set_iter lhsp_end = lhsp.end();
          for (set_iter iorg = lhsp.begin(); iorg != lhsp_end; ++iorg) {
            if (erules_.contains(*iorg, top_rhs))
              continue;
            for (set_iter idst = rhsc.begin(); idst != rhsc_end; ++idst) {
              if (*idst != top_rhs)
                erules_.insert(*iorg, *idst);
            }
            erules_.insert(*iorg, top_rhs);
          }

          // Add op -> state transitions that use top pending rule.
          typedef std::set<op_t>::const_iterator op_iter;
          const std::set<op_t>& lhsops = idrules_.parents(top_lhs);
          op_iter lhsops_end = lhsops.end();
          for (op_iter iop = lhsops.begin(); iop != lhsops_end; ++iop) {
            if (idrules_.contains(*iop, top_rhs))
              continue;
            for (set_iter idst = rhsc.begin(); idst != rhsc_end; ++idst) {
              // Add *iop -> *idst (may throw)
              if (*idst != top_rhs)
                private_add(std::make_pair(*iop, *idst));
            }
            private_add(std::make_pair(*iop, top_rhs));
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
      mutable bi_graph_t<state_t, state_t> erules_;
      /**
       * Bidirectional graph for the constant -> state rules in the
       * automaton.  Note that we really don't need the bidirectional
       * capabilities here.  We could make do with a map that merely 
       * mapped states to the identies that can reach them.
       */
      mutable bi_graph_t<op_t, state_t> idrules_;
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
     * Returns true if rhs of rule is reachable from lhs of rule in closure.
     * \relates epsilon_closure_t
     */
    bool is_reachable(const epsilon_closure_t& closure,
                      const idrule_t& rule) {
      return reachables(closure, lhs(rule)).count(rhs(rule)) > 0;
    }

    /**
     * Returns true if rhs of rule is reachable from lhs of rule in closure.
     * \relates epsilon_closure_t
     */
    bool is_reachable(const epsilon_closure_t& closure,
                      const erule_t& rule) {
      return reachables(closure, lhs(rule)).count(rhs(rule));
    }
 
    /**
     * Returns the set of states reachable from state in closure.
     * \relates epsilon_closure_t
     */
    inline
    const std::set<state_t>&
          reachables(const epsilon_closure_t& closure, const state_t& lhs) {
      closure.add_self_loop(lhs);
      closure.process_pending();
      return closure.erules_.children(lhs);
    }
 
    /**
     * Returns the set of states reachable from constant op in closure.
     * \relates epsilon_closure_t
     */
    inline
    const std::set<state_t>& 
          reachables(const epsilon_closure_t& closure, const op_t& op) {
      closure.process_pending();
      return closure.idrules_.children(op);
    }

    /**
     * Adds a transition from lhs -> rhs to closure.
     * \relates epsilon_closure_t
     */
    inline
    void add(epsilon_closure_t& closure, const erule_t& erule) {
      closure.add_self_loop(lhs(erule));
      closure.add_self_loop(rhs(erule));
      // Make sure erules contains self inverse for lhs and rhs.
      if (!is_reachable(closure, erule))
        closure.pending_.push(erule);
    }
 
    /**
     * Adds a transition from op -> rhs to closure.
     * \relates epsilon_closure_t
     */
    inline
    void add(epsilon_closure_t& closure, const idrule_t& rule) {
      check_constant(lhs(rule));
      check_equal(output(lhs(rule)), kind(rhs(rule)));
      closure.add_self_loop(rhs(rule));
      if (!is_reachable(closure, rule))
        closure.private_add(rule);
    }
 
    /**
     * Adds a transition bin_op(lhs1, lhs2) -> rhs to closure.
     * \relates epsilon_closure_t
     */
    inline
    void add_guarded(epsilon_closure_t& closure, 
                     const idrule_t& guard, const erule_t& erule) {
      if (is_reachable(closure, guard)) {
        add(closure, erule);
      } else {
        closure.watched_rules_[guard].insert(erule);
      }
    }
  }
}
#endif
