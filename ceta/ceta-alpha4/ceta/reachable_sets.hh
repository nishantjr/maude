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
#ifndef _reachable_sets_hh_
#define _reachable_sets_hh_

#include <deque>
#include <map>
#include <set>
#include <iostream>
#include <boost/none.hpp>
#include "trans_closure.hh"

namespace ceta {
  typedef std::pair<std::set<state_t>, term_t> reachable_t;

  /** Maintains list of reachable state sets, and adds new sets to queue. */
  class reachable_sets_t {
  public:
    reachable_sets_t(const ta_t& ta,
                     const std::set<state_t>& pos_states,
                     const std::set<state_t>& neg_states,
                     std::deque<reachable_t>& queue)
      : theory_(theory(ta)),
        pos_states_(pos_states),
        neg_states_(neg_states),
        queue_(queue) {
      // Build edge_map.
      typedef std::map<state_t, std::set<state_t> > edge_map_t;
      edge_map_t edge_map;
      {
        typedef ta_t::erule_iterator iter;
        iter iend = erules_end(ta);
        for (iter i = erules_begin(ta); i != iend; ++i)
          edge_map[rhs(*i)].insert(lhs(*i));
      }
      {
        typedef ta_t::rule_iterator iter;
        iter iend = rules_end(ta);
        for (iter i = rules_begin(ta); i != iend; ++i)
          edge_map[rhs(*i)].insert(lhs_states_begin(*i), lhs_states_end(*i));
      }
      transitive_closure(edge_map, pos_states_);
      transitive_closure(edge_map, neg_states_);
    }

    void add(const std::set<state_t>& states, const term_t& term) {
      reachable_rec_t rec(theory_, pos_states_, neg_states_,
                          states, root(term));
      map_t::iterator imap = map_.find(rec.both_rstates());
      if (imap == map_.end()) {
        // Set if bound to an associative operator or an identity.
        map_[rec.both_rstates()].push_back(rec);
        queue_.push_back(reachable_t(states, term));
      } else {
        reachable_vector_t& v = imap->second;
        typedef reachable_vector_t::iterator iter;
        bool new_subsumed = false;
        iter i = v.begin();
        while (!new_subsumed && (i != v.end())) {
          compare_action_t a = i->compare(theory_, rec);
          switch (a) {
          case incomparable:
            ++i;
            break;
          case subsumes:
            new_subsumed = true;
            break;
          case subsumed_by:
            // This element has been subsumed, so remove it by overwritting
            // it with last element.
            *i = v.back();
            v.pop_back();
            break;
          case set_none:
            i->set_op_none();
            queue_.push_back(reachable_t(states, term));
            new_subsumed = true;
            break;
          }
        }
        if (!new_subsumed) {
          map_[rec.both_rstates()].push_back(rec);
          queue_.push_back(reachable_t(states, term));
        }
      }
    }

    bool contains(const std::set<state_t>& states, const op_t& op) const {
      reachable_rec_t rec(theory_, pos_states_, neg_states_, states, op);
      map_t::const_iterator imap = map_.find(rec.both_rstates());
      if (imap == map_.end()) {
        return false;
      } else {
        const reachable_vector_t& v = imap->second;
        typedef reachable_vector_t::const_iterator iter;
        bool subsumed = false;
        for (iter i = v.begin(); !subsumed && (i != v.end()); ++i) {
          compare_action_t a = i->compare(theory_, rec);
          if ((a == subsumes) || (a == set_none))
            subsumed = true;
        }
        return subsumed;
      }
    }
  private:

    reachable_sets_t(const reachable_sets_t& sets);
    reachable_sets_t& operator=(const reachable_sets_t& sets);

    /**
     * Compares the ranges [ibegin iend) and [jbegin jend) which are
     * assumed to contain elements in sorted order, and sets i_subset_j to
     * false if the elements in [ibegin iend) are not a subset of the
     * elements in [jbegin jend), and sets j_subset_i to false if the
     * elements in [jbegin jend) are not a subset of [ibegin iend).
     */
    template<typename Iterator>
    static
    void compare_sorted_ranges(Iterator ibegin, Iterator iend,
                               Iterator jbegin, Iterator jend,
                               bool& i_subset_j,
                               bool& j_subset_i) {
      Iterator i = ibegin;
      Iterator j = jbegin;
      while ((i_subset_j || j_subset_i) && (i != iend) && (j != jend)) {
         // if i points to state before j.
         if (*i < *j) {
           i_subset_j = false;
            ++i;
         // if j points to state before i
        } else if (*j < *i) {
          j_subset_i = false;
          ++j;
        } else { // *i == *j
          ++i;
          ++j;
        }
      }
      // If i contains more elements at end than j.
      if (i != iend) i_subset_j = false;
      // if j contains more elements at end than i.
      if (j != jend) j_subset_i = false;
    }

    enum compare_action_t {
      incomparable, subsumes, subsumed_by, set_none };

    /**
     * Stores which positive and negative states are reachable for a
     * particular set of positive and negative states.
     */
    class reachable_rec_t {
    public:
      reachable_rec_t(const theory_t& theory,
                      const std::set<state_t>& pos_states,
                      const std::set<state_t>& neg_states,
                      const std::set<state_t>& states,
                      const boost::optional<op_t>& op) {
       // Split states into both, positive, and negative.
       typedef std::set<state_t>::const_iterator iter;
       for (iter i = states.begin(); i != states.end(); ++i) {
         bool is_pos = pos_states.count(*i) > 0;
         bool is_neg = neg_states.count(*i) > 0;
         if (is_pos && is_neg) {
           both_rstates_.push_back(*i);
         } else if (is_pos) {
           pos_rstates_.push_back(*i);
         } else if (is_neg) {
           neg_rstates_.push_back(*i);
         }
       }
       if (op && (is_assoc(axioms(theory, *op)) || is_identity(theory, *op)))
         op_ = op;
      }

      const std::vector<state_t> both_rstates(void) const {
        return both_rstates_;
      }

      void set_op_none(void) {
        op_ = boost::none;
      }

      /**
       * Compares this reachable record with r.  The result of this
       * comparison can be "incomparable" if they neither subsumes the other,
       * "subsumes" if this record subsumes r, "subsumed_by" if this record
       * is subsumed by r, and set_null if the two records have identical
       * postive and negative states, and the effect of mergeing the records
       * means that op should be set to boost::none.
       */
      compare_action_t compare(const theory_t& theory,
                               const reachable_rec_t& r) const {
        bool could_subsume = true;
        bool could_be_subsumed = true;
        // Check pos_states.
        compare_sorted_ranges(pos_rstates_.begin(), pos_rstates_.end(),
                              r.pos_rstates_.begin(), r.pos_rstates_.end(),
                              could_be_subsumed, could_subsume);
        compare_sorted_ranges(neg_rstates_.begin(), neg_rstates_.end(),
                              r.neg_rstates_.begin(), r.neg_rstates_.end(),
                              could_subsume, could_be_subsumed);
        if (!could_subsume && !could_be_subsumed) {
          return incomparable;
        } else if (could_subsume && !op_) {
          return subsumes;
        } else if (could_be_subsumed && !r.op_) {
          return subsumed_by;
        } else if (!op_ || !r.op_) {
          return incomparable;
        } else if (could_subsume && (*op_ == *r.op_)) {
          return subsumes;
        } else if (could_subsume
                && is_identity_of(theory, *op_, *r.op_)) {
          return subsumes;
        } else if (could_be_subsumed && (*op_ == *r.op_)) {
          return subsumed_by;
        } else if (could_be_subsumed
                && is_identity_of(theory, *r.op_, *op_)) {
          return subsumed_by;
        } else if (could_subsume && could_be_subsumed) {
          return set_none;
        } else {
          return incomparable;
        }
      };
    private:
      /** Returns true if id is the identity of op in theory. */
      static
      bool is_identity_of(const theory_t& theory, const op_t& op,
                          const op_t& id) {
        const axiom_set_t& cur_axioms = axioms(theory, op);
        return id_symbol(cur_axioms)
            && (*id_symbol(cur_axioms) == id);
      }
      std::vector<state_t> both_rstates_;
      std::vector<state_t> pos_rstates_;
      std::vector<state_t> neg_rstates_;
      boost::optional<op_t> op_;
    };

    typedef std::vector<reachable_rec_t> reachable_vector_t;


    typedef std::map< std::vector<state_t>, reachable_vector_t> map_t;

    theory_t theory_;
    /** Stores states marked as positive. */
    std::set<state_t> pos_states_;
    /** Stores states marked as negative. */
    std::set<state_t> neg_states_;

    map_t map_;
    std::deque<reachable_t>& queue_;
  };
}

#endif
