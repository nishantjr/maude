/* Copyright 2007 University of Illinois at Urbana-Champaign
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
#ifndef ac_parser_hh_
#define ac_parser_hh_
/** \file
 * \brief
 * Defines class for checking whether a multiset belongs is in the
 * commutative image of a context-free language.
 */

#include <map>
#include <set>
#include <vector>
#include <iostream>
#include <stdexcept>

#include "cfg.hh"
#include "ldsolver.hh"
#include "trans_closure.hh"

namespace ceta {


template<typename Nonterminal>
class ac_parser_t {
public:
  typedef std::set<Nonterminal> nt_set_t;

  /** Creates a parser with an empty grammar. */
  ac_parser_t(void) {
  }

  /** Adds nonterminal to parser.  Returns true if it was new. */
  bool add_nonterminal(const Nonterminal& n) {
    bool should_add = (nt_indices_.count(n) == 0);
    if (should_add) {
      nt_indices_[n] = nonterminals_.size();
      nonterminals_.push_back(n);
    }
    return should_add;
  }

  const std::vector<Nonterminal>& nonterminals(void) const {
    return nonterminals_;
  }

  /** Adds rule lhs := rhs1 rhs2 to parser. */
  void add_rule(const Nonterminal& lhs,
                const Nonterminal& rhs1,
                const Nonterminal& rhs2) {
    size_t ilhs = nt_index(lhs);
    size_t irhs1 = nt_index(rhs1);
    size_t irhs2 = nt_index(rhs2);

    std::set<size_t>& cur_set = edge_map_[ilhs];
    cur_set.insert(irhs1);
    cur_set.insert(irhs2);
    rules_.push_back(cfg::rrule_t<size_t>(ilhs, irhs1, irhs2));
  }

  /** Adds rule lhs := rhs to parser. */
  void add_erule(const Nonterminal& lhs, const Nonterminal& rhs) {
    size_t ilhs = nt_index(lhs);
    size_t irhs = nt_index(rhs);
    edge_map_[ilhs].insert(irhs);
    erules_.push_back(cfg::urule_t<size_t>(ilhs, irhs));
  }

  /**
   * Returns complete set of nonterminals which generate a multiset with the
   * given elements.
   */
  const nt_set_t parse(const std::map<nt_set_t, size_t>& counts) const {
    // There is an equation for each nonterminal and element in counts.
    size_t eqn_count = nonterminals_.size() + counts.size();
    size_t var_count = rules_.size() + erules_.size();
    // Add variables for each element of each set in counts.
    typedef std::map<nt_set_t, size_t> counts_t;
    typedef typename counts_t::const_iterator count_iter;
    for (count_iter i = counts.begin(); i != counts.end(); ++i)
      var_count += (i->first).size();

    // Create coefficients vector.
    // This is in column major form, so we should populate coefficients
    // for each rule in order.
    std::vector<int> coef(eqn_count * var_count, 0);
    int* p_coef = &coef[0];

    std::vector<Nonterminal> rule_lhs;
    rule_lhs.reserve(var_count);

    // Add coefficients for regular rules.
    typedef typename rules_t::const_iterator rule_iter;
    for (rule_iter i = rules_.begin(); i != rules_.end(); ++i) {
      --p_coef[i->lhs];
      ++p_coef[i->rhs1];
      ++p_coef[i->rhs2];
      p_coef += eqn_count;
    }

    // Add coefficients for epsilon rules.
    typedef typename erules_t::const_iterator erule_iter;
    for (erule_iter i = erules_.begin(); i != erules_.end(); ++i) {
      --p_coef[i->lhs];
      ++p_coef[i->rhs];
      p_coef += eqn_count;
    }

    // Add coefficents for terminal rules.
    {
      size_t term_index = nonterminals_.size();
      for (count_iter i = counts.begin(); i != counts.end(); ++i) {
        const nt_set_t& cur_set = i->first;
        typedef typename nt_set_t::const_iterator set_iter;
        for (set_iter j = cur_set.begin(); j != cur_set.end(); ++j) {
          --p_coef[nt_index(*j)];
          ++p_coef[term_index];
          p_coef += eqn_count;
        }
        ++term_index;
      }
    }

    // Coefficients of solution.
    std::vector<int> v(nonterminals_.size(), 0);

    // Initialize terminal values from counts.
    for (count_iter i = counts.begin(); i != counts.end(); ++i) {
      v.push_back(i->second);
    }

    // Commented out logging code for debugging.
    // Print coeffs
    //{
    //  count_iter ic = counts.begin();
    //  for (size_t i = 0; i != eqn_count; ++i) {
    //    for (size_t j = 0; j != var_count; ++j) {
    //      int v = coef[i + j * eqn_count];
    //      if ((0 <= v) && (v <= 9)) std::cerr << " ";
    //      std::cerr << v;
    //    }
    //    std::cerr << " = " << v[i] << " (";
    //    if (i < nonterminals_.size()) {
    //      std::cerr << nonterminals_[i];
    //    } else {
    //      const nt_set_t& set = ic->first;
    //      std::cerr << "{";
    //      if (!set.empty()) {
    //        typedef typename nt_set_t::const_iterator set_iter;
    //        set_iter i = set.begin();
    //        std::cerr << *i;
    //        ++i;
    //        for (; i != set.end(); ++i)
    //          std::cerr << ", " << *i;
    //      }
    //      std::cerr << "}";
    //      ++ic;
    //    }
    //    std::cerr << ")" << std::endl;
    //  }
    //}

    std::set<Nonterminal> result;
    ceta::ld_solver_t solver(eqn_count, var_count, &(coef[0]));
    std::vector<unsigned> sol(var_count,0);

    // Check that the system has no homogeneous solutions.
    // This should only occur if ther epsilon closure has cycles, which
    // is explicitly not allowed.
    if (solver.next(sol)) {
      std::cerr << "Cycle detected" << std::endl;
      throw std::logic_error("Cycles detected");
    }

    // Try solving non-homogenous solution for each coefficient.
    for (size_t in = 0; in != nonterminals_.size(); ++in) {
      const Nonterminal& cur_nt = nonterminals_[in];
      v[in] = -1;
      solver.solve(&v[0]);
      bool added = false;
      while (!added && solver.next(sol)) {
        // Compute reachable nonterminals.
        std::set<size_t> reachables;
        reachables.insert(in);
        transitive_closure(edge_map_, reachables);

        // Set to true because we have not found an unreachable lhs.
        added = true;

        // Get left-hand-side of all used rules.
        typedef std::vector<unsigned>::const_iterator sol_iter;
        sol_iter isol = sol.begin();

        rule_iter r_end = rules_.end();
        for (rule_iter i = rules_.begin(); added && (i != r_end); ++i) {
          added = (*isol == 0) || (reachables.count(i->lhs) > 0);
          ++isol;
        }

        erule_iter e_end = erules_.end();
        for (erule_iter i = erules_.begin(); added && (i != e_end); ++i) {
          added = (*isol == 0) || (reachables.count(i->lhs) > 0);
          ++isol;
        }
        if (added) result.insert(cur_nt);
      }
      v[in] = 0;
    }
    return result;
  }
private:
  /**
   * Returns index of nonterminal.
   * @param nt Nonterminal to return index for.  This should have already
   *           been aded to parser.
   */
  size_t nt_index(const Nonterminal& nt) const {
    return nt_indices_.find(nt)->second;
  }

  /** Vector of nonterminals used for identifying indices. */
  std::vector<Nonterminal> nonterminals_;

  /** Type for nt_indices_. */
  typedef std::map<Nonterminal, size_t> nt_indices_t;

  /** Maps each nonterminal to it's index.  */
  nt_indices_t nt_indices_;

  typedef std::vector< cfg::rrule_t<size_t> > rules_t;

  /** Maps each rule index to the nonterminal on it's left-hand-side. */
  rules_t rules_;

  typedef std::vector< cfg::urule_t<size_t> > erules_t;

  erules_t erules_;

  typedef std::map<size_t, std::set<size_t> > edge_map_t;

  edge_map_t edge_map_;
};

}
#endif
