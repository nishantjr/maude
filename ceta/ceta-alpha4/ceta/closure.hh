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

#include "ta.hh"
#include "earley.hh"
#include <map>

namespace ceta {
  /**
   * Provides information about the reachability relation between different
   * states in the automaton.  This includes edges from epsilon transitions
   * as well as edges induced by identities.
   */
  class closure_t {
    typedef std::map<op_t, std::set<state_t> > crules_t;
    typedef std::map<state_t, std::set<state_t> > equiv_classes_t;
    typedef std::map<state_t, state_t> representatives_t;
    typedef std::map<state_t, std::set<state_t> > edge_map_t;
    typedef std::map<op_t, std::vector<rule_t> > rule_map_t;
    friend std::ostream& operator<<(std::ostream& o, const closure_t& c);
  public:
    /** Constructs an epsilon transition graph with no transitions. */
    closure_t(const ta_t& ta);

    /** Returns set of representative states reachable from constant.  */
    const std::set<state_t>& reachables(const op_t& op) const {
      crules_t::const_iterator i = crules_.find(op);
      if (i != crules_.end()) {
        return i->second;
      } else {
        static const std::set<state_t> empty_set;
        return empty_set;
      }
    }

    /**
     * If the state belongs to a strongly connected component, then this
     * function returns a "representative" of the state.  Otherwise, this
     * returns the input state.
     */
    const state_t& representative(const state_t& s) const {
      representatives_t::const_iterator i = representatives_.find(s);
      return (i != representatives_.end()) ? i->second : s;
    }

    /**
     * Returns minimal set of representative states that can reach every
     * state in the input.
     * We require that the set is closed with respect to reachability, i.e.
     *  x \in set /\ x ->* y => y \in set
     */
    const std::set<state_t>
    coverage_set(const std::set<state_t>& set) const {
      std::set<state_t> result;
      typedef std::set<state_t>::const_iterator iter;
      for (iter i = set.begin(); i != set.end(); ++i) {
        if (representative(*i) == *i) {
          const std::set<state_t>& edges = in_edges(*i);
          if (!overlap(edges, set))
            result.insert(*i);
        }
      }
      return result;
    }

    /**
     * Returns representative states that reach state from an incoming edge
     * s' is in in_edges(s) iff there is an edge s' -> s.
     */
    const std::set<state_t>& in_edges(const state_t& s) const {
      edge_map_t::const_iterator i = in_edges_.find(s);
      if (i != in_edges_.end()) {
        return i->second;
      } else {
        static std::set<state_t> empty_set;
        return empty_set;
      }
    }

    /**
     * Returns representative states that can be reached from state via
     * outgoing edge.
     * s' is in out_edges(s) iff there is an edge s -> s'.
     */
    const std::set<state_t>& out_edges(const state_t& s) const {
      edge_map_t::const_iterator i = out_edges_.find(s);
      if (i != out_edges_.end()) {
        return i->second;
      } else {
        static std::set<state_t> empty_set;
        return empty_set;
      }
    }

    /**
     * Adds state and all representative states reachable from
     * state to set. The set is assumed to be closed with respect to
     * reachability, i.e. x \in set /\ x ->* y => y \in set
     */
    void add_and_close(std::set<state_t>& set, const state_t& s) const {
      std::vector<state_t> stack;
      stack.push_back(s);
      while (!stack.empty()) {
        state_t next = stack.back();
        stack.pop_back();
        bool added = set.insert(next).second;
        if (added) {
          // Add next edges to stack
          edge_map_t::const_iterator io = out_edges_.find(next);
          if (io != out_edges_.end()) {
            stack.insert(stack.end(), io->second.begin(), io->second.end());
          }
        }
      }
    }

    /**
     * Adds all representative states reachable from states in range
     * [begin end) to set.
     */
    template<typename Iterator>
    void add_and_close_all(std::set<state_t>& set,
            const Iterator& begin, const Iterator& end) const {
      for (Iterator i = begin; i != end; ++i)
        add_and_close(set, *i);
    }

    /**
     * Returns set containing all elements that are represented by an
     * element in set.
     */
    const std::set<state_t> full_set(const std::set<state_t>& set) const {
      std::set<state_t> result;

      typedef std::set<state_t>::const_iterator set_iter;
      for (set_iter is = set.begin(); is != set.end(); ++is) {
        typedef equiv_classes_t::const_iterator class_iter;
        result.insert(*is);
        class_iter ic = equiv_classes_.find(*is);
        if (ic != equiv_classes_.end())
          result.insert(ic->second.begin(), ic->second.end());
      }
      return result;
    }

    /**
     * Returns rules for given operator.  The rules have been modified so
     * that only states that representatives appear in rules.
     */
    const std::vector<rule_t>& op_rules(const op_t& op) const {
      static const std::vector<rule_t> empty_vector;
      rule_map_t::const_iterator i = rule_map_.find(op);
      return (i == rule_map_.end())
           ? empty_vector
           : i->second;
    }
  private:
    // Disable copy construction and assignment
    closure_t(const closure_t& closure);
    closure_t& operator=(const closure_t& closure);

    /** Returns true if two sets contain a common state. */
    static
    bool overlap(const std::set<state_t>& x, const std::set<state_t>& y) {
      typedef std::set<state_t>::const_iterator iter;
      iter ix = x.begin();
      iter xend = x.end();
      iter iy = y.begin();
      iter yend = y.end();
      bool result = false;
      while (!result && (ix != xend) && (iy != yend)) {
        if (*ix < *iy) {
          ++ix;
        } else if (*iy < *ix) {
          ++iy;
        } else {
          result = true;
        }
      }
      return result;
    }

    equiv_classes_t equiv_classes_;
    representatives_t representatives_;
    crules_t crules_;
    edge_map_t in_edges_;
    edge_map_t out_edges_;
    rule_map_t rule_map_;
  };

  inline
  std::ostream& operator<<(std::ostream& o, const closure_t& c) {
    typedef std::set<state_t>::const_iterator set_iter;

    {
      o << "Equivalence classes: " << std::endl;
      typedef closure_t::equiv_classes_t::const_iterator iter;
      iter iend = c.equiv_classes_.end();
      for (iter i = c.equiv_classes_.begin(); i != iend; ++i)
        o << i->first << " : " << i->second << std::endl;
    }
    {
      o << "Representatives: " << std::endl;
      typedef closure_t::representatives_t::const_iterator iter;
      iter iend =   c.representatives_.end();
      for (iter i = c.representatives_.begin(); i != iend; ++i)
        o << i->first << " -> " << i->second << std::endl;
    }
    {
      o << "Crules: " << std::endl;
      typedef closure_t::crules_t::const_iterator iter;
      iter iend = c.crules_.end();
      for (iter i = c.crules_.begin(); i != iend; ++i)
        o << i->first << " -> " << i->second << std::endl;
    }
    {
      o << "In edges: " << std::endl;
      typedef closure_t::edge_map_t::const_iterator iter;
      iter iend = c.in_edges_.end();
      for (iter i = c.in_edges_.begin(); i != iend; ++i)
        o << i->first << " <- " << i->second << std::endl;
    }
    {
      o << "Out edges: " << std::endl;
      typedef closure_t::edge_map_t::const_iterator iter;
      iter iend = c.out_edges_.end();
      for (iter i = c.out_edges_.begin(); i != iend; ++i)
        o << i->first << " -> " << i->second << std::endl;
    }
    return o;
  }

  /**
   * Constructs a new data structure with context free rules for a specific
   * associative operator.
   *
   * Rules must be a class with the following methods:
   *   Rules():
   *     Constructs empty set of rules.
   *   bool Rules.add_nonterminal(state_t):
   *     Adds state as nonterminal, returning true if it is new.
   *   Rules.add_rule(state_t rhs, state_t, lhs1, state_t lhs2):
   *     Adds rule "rhs := lhs1 lhs2" to Rules.
   *   Rules.add_erule(state_t rhs, state_t lhs):
   *     Add rule "rhs := lhs" to rules.
   *   Rules.nonterminals(): Returns container with the nonterminals.
   */
  template<typename Rules>
  const Rules make_rules(const closure_t& closure, const op_t& op) {
    Rules result;
    // Iterate through rules adding rule as necessary.
    std::vector<rule_t> rules = closure.op_rules(op);
    typedef std::vector<rule_t>::const_iterator rule_iter;
    for (rule_iter i = rules.begin(); i != rules.end(); ++i) {
      state_t first_state  = lhs_state(*i, 0);
      state_t second_state = lhs_state(*i, 1);

      result.add_nonterminal(first_state);
      result.add_nonterminal(second_state);
      result.add_nonterminal(rhs(*i));
      result.add_rule(rhs(*i), first_state, second_state);
    }

    std::vector< cfg::cfg_erule_t<state_t> > erules;
    // Add epsilon rules.
    std::vector<state_t> queue(result.nonterminals().begin(),
                               result.nonterminals().end());
    while (!queue.empty()) {
      state_t lhs = queue.back();
      queue.pop_back();
      const std::set<state_t>& rhs_set = closure.out_edges(lhs);
      typedef std::set<state_t>::const_iterator set_iter;
      for (set_iter i = rhs_set.begin(); i != rhs_set.end(); ++i) {
        bool added = result.add_nonterminal(*i);
        if (added)
          queue.push_back(*i);
        result.add_erule(*i, lhs);
      }
    }
    return result;
  }
}
#endif
