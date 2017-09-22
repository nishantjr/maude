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
#ifndef _subset_construction_hh_
#define _subset_construction_hh_
/** \file
 * \brief
 * Defines interface for subset construction and checking emptiness.
 */

#include <ceta/export.h>
#include <ceta/ta.hh>

/** Namespace for all of Ceta's declarations. */
namespace ceta {
  /** Result of testing the emptiness of a tree automaton. */
  class CETA_DSO_EXPORT test_result_t {
  public:
    /** Constructs result indicating property is satisified. */
    test_result_t() {
    }
    /**
     * Constructs result indicating property is not satisified and provided
     * term as a counterexample.
     */
    test_result_t(const term_t& term, const std::set<state_t>& set)
      : impl_(make_pair(term, set)) {
      check_kinds(kind(term), set);
    }
    /**
     * Converts result to a boolean that is true if the property is
     * satisfied.
     */
    operator bool() {
      return !impl_;
    }
  private:
    typedef std::set<state_t> set_t;
    friend const term_t& counterexample(const test_result_t& result);
    friend
    const std::set<state_t>& reachable_set(const test_result_t& result);
    /** Pointer to accepted term or null if the property is satisfied. */
    boost::optional< std::pair<term_t, set_t> > impl_;
  };

  /**
   * Returns counterexample of property.
   * \relates test_result_t
   */
  inline
  const term_t& counterexample(const test_result_t& result) {
    return result.impl_->first;
  }
  /**
   * Returns reachable set of counterexample.
   * \relates test_result_t
   */
  inline
  const std::set<state_t>& reachable_set(const test_result_t& result) {
    return result.impl_->second;
  }

  class subset_constructor_impl;

  /** Performs subset construction using the rules in the tree automaton. */
  class CETA_DSO_EXPORT subset_constructor_t {
  public:
    subset_constructor_t(const ta_t& ta);
    /** Performs some finite amount of work in subset construction. */
    void work(void);
    /** Returns true if subset construction has found all reachable sets. */
    bool is_complete(void) const;
    /** Returns true if constructor has a new reachable set. */
    bool has_next(void) const;
    /** Returns next reachable set. */
    const std::set<state_t>& next_set(void) const;
    /** Returns term for next reachable set. */
    const term_t& next_term(void) const;
    /** Pops next reachable set from queue. */
    void pop_next(void);
  private:
    /** Disable copy constructor. */
    subset_constructor_t(const subset_constructor_t&);
    /** Disable assignment. */
    subset_constructor_t& operator=(const subset_constructor_t&);
    /** Pointer to implementation. */
    boost::shared_ptr<subset_constructor_impl> impl_;
  };

  /**
   * Checks if no term is accepted.
   * \relates ta_t
   */
  inline
  const test_result_t test_emptiness(const ta_t& ta) {
    subset_constructor_t sc(ta);
    while (sc.has_next() || !sc.is_complete()) {
      if (!sc.has_next())
        sc.work();
      while (sc.has_next()) {
        const std::set<state_t>& set = sc.next_set();
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
#endif
