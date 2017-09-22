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
/** \file
 * \brief Implementation for closure_t
 */

#include "closure.hh"
#include <iostream>

namespace ceta {
namespace closure {
  typedef std::map<state_t, std::set<op_t> > state_op_map_t;
  typedef std::pair<op_t, state_t> idrule_t;
  typedef std::map<state_t, std::set<erule_t> > watch_map_t;
  typedef std::map<op_t, watch_map_t> guard_map_t;
  typedef std::map<state_t, std::set<state_t> > edge_map_t;
  typedef std::map<op_t, std::set<state_t> > crules_t;

  void add(const edge_map_t& out_edges,
           watch_map_t& watch_map,
           std::set<state_t>& op_states,
           state_op_map_t& state_op_map,
           std::vector<erule_t>& pending,
           const op_t& op,
           const state_t& state) {
    std::vector<state_t> stack;
    stack.push_back(state);
    while (!stack.empty()) {
      state_t cur = stack.back();
      stack.pop_back();
      bool added = op_states.insert(cur).second;
      if (added) {
        state_op_map[cur].insert(op);
        // Add out_edges[cur] to stack
        {
          edge_map_t::const_iterator i = out_edges.find(cur);
          if (i != out_edges.end()) {
            const std::set<state_t>& edges = i->second;
            stack.insert(stack.end(), edges.begin(), edges.end());
          }
        }
        // Determine if guards can be dropped.
        {
          watch_map_t::iterator i = watch_map.find(cur);
          if (i != watch_map.end()) {
            const std::set<erule_t>& rules = i->second;
            pending.insert(pending.end(), rules.begin(),rules.end());
            watch_map.erase(i);
          }
        }
      }
    }
  }

  /** Propagates pending edges to update arguments and crules_. */
  void propagate(edge_map_t& out_edges,
                 guard_map_t& guard_map,
                 crules_t& crules,
                 state_op_map_t& state_op_map,
                 std::vector<erule_t>& pending) {
    while (!pending.empty()) {
      const erule_t erule = pending.back();
      pending.pop_back();
      const state_t& rhs1 = rhs(erule);
      bool added = out_edges[lhs(erule)].insert(rhs1).second;
      if (added) {
        state_op_map_t::const_iterator i
                = state_op_map.find(lhs(erule));
        if (i != state_op_map.end()) {
          typedef std::set<op_t>::const_iterator iter;
          const std::set<op_t>& new_ops = i->second;
          iter iend = new_ops.end();
          for (iter i = new_ops.begin(); i != iend; ++i) {
            add(out_edges, guard_map[*i], crules[*i], state_op_map, pending,
                *i, rhs1);
          }
        }
      }
    }
  }

  struct dfs_state_t {
    typedef std::set<state_t>::const_iterator iterator;
    dfs_state_t(const state_t& astate, const std::set<state_t>& set)
      : state(astate),
        begin(set.begin()),
        end(set.end()) {
    }

    state_t state;
    iterator begin;
    iterator end;
  };

  /** Adds reversed edges from input to output. */
  void reverse_map(const edge_map_t& input, edge_map_t& output) {
    typedef edge_map_t::const_iterator iter;
    for (iter i = input.begin(); i != input.end(); ++i) {
      typedef std::set<state_t>::const_iterator set_iter;
      set_iter jend = i->second.end();
      for (set_iter j = i->second.begin(); j != jend; ++j)
        output[*j].insert(i->first);
    }
  }

  /**
   * Performs depth-first search of states and pushes each state to vector
   * after exploring it's children.
   */
  template<typename StateIterator>
  void finish_times(StateIterator states_begin, StateIterator states_end,
                    edge_map_t& out_edges,
                    std::vector<state_t>& finish_stack) {
    std::set<state_t> unexplored(states_begin, states_end);
    while (unexplored.size() > 0) {
      state_t next = *unexplored.begin();
      typedef std::set<state_t>::const_iterator set_iter;
      std::vector<dfs_state_t> dfs_stack;
      unexplored.erase(unexplored.begin());
      dfs_stack.push_back(dfs_state_t(next, out_edges[next]));
      while (!dfs_stack.empty()) {
        set_iter ibegin = dfs_stack.back().begin;
        set_iter iend = dfs_stack.back().end;
        if (ibegin != iend) {
          ++dfs_stack.back().begin;
          if (unexplored.erase(*ibegin) > 0) {
            dfs_stack.push_back(dfs_state_t(*ibegin, out_edges[*ibegin]));
          }
        } else {
          state_t cur = dfs_stack.back().state;
          finish_stack.push_back(cur);
          dfs_stack.pop_back();
        }
      }
    }
  }

  /**
   * Performs depth-first search of states and pushes each state to vector
   * after exploring it's children.
   */
  void find_cycles(edge_map_t& in_edges,
                   std::vector<state_t>& finish_stack,
                   std::map<state_t, std::set<state_t> >& equiv_classes) {
    std::set<state_t> unexplored(finish_stack.begin(), finish_stack.end());
    while (!unexplored.empty()) {
      state_t next = finish_stack.back();
      finish_stack.pop_back();
      if (unexplored.erase(next) == 0)
        continue;
      std::vector<dfs_state_t> dfs_stack;
      dfs_stack.push_back(dfs_state_t(next, in_edges[next]));
      std::set<state_t>& eclass = equiv_classes[next];
      while (!dfs_stack.empty()) {
        typedef std::set<state_t>::const_iterator set_iter;
        set_iter ibegin = dfs_stack.back().begin;
        set_iter iend = dfs_stack.back().end;
        if (ibegin != iend) {
          ++dfs_stack.back().begin;
          if (unexplored.erase(*ibegin) > 0)
            dfs_stack.push_back(dfs_state_t(*ibegin, in_edges[*ibegin]));
        } else {
          state_t cur = dfs_stack.back().state;
          if (cur != next)
            eclass.insert(cur);
          dfs_stack.pop_back();
        }
      }
    }
  }
  void add_representatives(const edge_map_t& input,
                           const std::map<state_t, state_t>& reps,
                           edge_map_t& output) {
    typedef edge_map_t::const_iterator iter;
    for (iter i = input.begin(); i != input.end(); ++i) {
      typedef std::map<state_t, state_t>::const_iterator map_iter;
      state_t state = i->first;
      map_iter imap = reps.find(i->first);
      state_t rep = (imap != reps.end()) ? imap->second : state;

      const std::set<state_t>& in_set = i->second;
      std::set<state_t>& out_set = output[rep];
      typedef std::set<state_t>::const_iterator set_iter;
      for (set_iter j = in_set.begin(); j != in_set.end(); ++j) {
        map_iter jmap = reps.find(*j);
        state_t rep = (jmap != reps.end()) ? jmap->second : *j;
        out_set.insert(rep);
      }
    }
  }
}

  using namespace ceta::closure;
    /** Constructs an epsilon transition graph with no transitions. */
  closure_t::closure_t(const ta_t& ta) {
    const theory_t& cur_theory = theory(ta);
    // Create edge map with out edges.
    edge_map_t out_edges;
    {
      typedef ta_t::erule_iterator iter;
      iter iend = erules_end(ta);
      for (iter i = erules_begin(ta); i != iend; ++i)
        out_edges[lhs(*i)].insert(rhs(*i));
    }
    // Initialize crules and out_edges from theory.
    {
      state_op_map_t state_op_map;
      guard_map_t guard_map;
      typedef ta_t::rule_iterator rule_iter;
      for (rule_iter i = rules_begin(ta); i != rules_end(ta); ++i) {
        const rule_t& rule = *i;
        const op_t& cur_op = op(rule);
        if (is_constant(cur_op)) {
          std::vector<erule_t> pending;
          add(out_edges, guard_map[cur_op], crules_[cur_op],
              state_op_map, pending, cur_op, rhs(rule));
          propagate(out_edges, guard_map, crules_, state_op_map, pending);
        } else if (is_binary(op(rule))) {
          axiom_set_t op_axioms = axioms(cur_theory, op(rule));
          const state_t& lhs1 = lhs_state(rule, 0);
          const state_t& lhs2 = lhs_state(rule, 1);
          const state_t& rhs1 = rhs(rule);
          boost::optional<op_t> id = id_symbol(op_axioms);

          switch (id_type(op_axioms)) {
          case id_none:
            break;
          case id_left:
            if (crules_[*id].count(lhs1) == 0) {
              guard_map[*id][lhs1].insert(erule_t(lhs2, rhs1));
            } else {
              std::vector<erule_t> pending;
              pending.push_back(erule_t(lhs2, rhs1));
              propagate(out_edges, guard_map, crules_, state_op_map,
                        pending);
            }
            break;
          case id_right:
            if (crules_[*id].count(lhs2) == 0) {
              guard_map[*id][lhs2].insert(erule_t(lhs1, rhs1));
            } else {
              std::vector<erule_t> pending;
              pending.push_back(erule_t(lhs1, rhs1));
              propagate(out_edges, guard_map, crules_, state_op_map,
                        pending);
            }
            break;
          case id_both:
            const std::set<state_t>& op_rules = crules_[*id];
            if (op_rules.count(lhs1) == 0) {
              guard_map[*id][lhs1].insert(erule_t(lhs2, rhs1));
            } else {
              std::vector<erule_t> pending;
              pending.push_back(erule_t(lhs2, rhs1));
              propagate(out_edges, guard_map, crules_, state_op_map,
                        pending);
            }
            if (op_rules.count(lhs2) == 0) {
              guard_map[*id][lhs2].insert(erule_t(lhs1, rhs1));
            } else {
              std::vector<erule_t> pending;
              pending.push_back(erule_t(lhs1, rhs1));
              propagate(out_edges, guard_map, crules_, state_op_map,
                        pending);
            }
            break;
          }
        }
      }
    }

    edge_map_t in_edges;
    reverse_map(out_edges, in_edges);

    // Compute strongly connected components
    {
      std::vector<state_t> finish_stack;
      finish_times(states_begin(ta), states_end(ta), out_edges,
                   finish_stack);
      //Construct reverse edge map.
      // Find cycles using in_edges and finish_stack
      find_cycles(in_edges, finish_stack, equiv_classes_);
      // Update represenatives from equiv_clases
      typedef equiv_classes_t::const_iterator class_iter;
      class_iter iend = equiv_classes_.end();
      for (class_iter i = equiv_classes_.begin(); i != iend; ++i) {
        state_t rep = i->first;
        typedef std::set<state_t>::const_iterator set_iter;
        set_iter jend = i->second.end();
        for (set_iter j = i->second.begin(); j != jend; ++j) {
          if (*j == rep) throw std::logic_error("Illegal");
          representatives_.insert(std::make_pair(*j, rep));
        }
      }
    }

    {
      typedef crules_t::iterator crule_iter;
      for (crule_iter i = crules_.begin(); i != crules_.end(); ++i) {
        std::set<state_t>& states = i->second;
        typedef std::set<state_t>::iterator iter;
        iter i = states.begin();
        while (i != states.end()) {
          // Erase *i if it is not a representative.
          if (representatives_.count(*i) > 0) {
            iter next = i;
            ++next;
            states.erase(i);
            i = next;
          } else {
            ++i;
          }
        }
      }
    }
    // Copy representatives only from in_edges to in_edges_ and
    //  out_edges to out_edges_.
    add_representatives(in_edges, representatives_, in_edges_);
    add_representatives(out_edges, representatives_, out_edges_);

    // Populate rule_map_ with rules from automaton.
    {
      typedef ta_t::rule_iterator rule_iter;
      for (rule_iter i = rules_begin(ta); i != rules_end(ta); ++i) {
        // This first replaces each state with it's representative.
        typedef rule_t::lhs_state_iterator iter;
        std::vector<state_t> inputs;
        inputs.reserve(lhs_state_count(*i));
        iter iend = lhs_states_end(*i);
        for (iter j = lhs_states_begin(*i); j != iend; ++j)
          inputs.push_back(representative(*j));
        state_t new_rhs = representative(rhs(*i));
        rule_t new_rule(op(*i), inputs.begin(), inputs.end(), new_rhs);
        rule_map_[op(*i)].push_back(new_rule);
      }
    }
  }
}
