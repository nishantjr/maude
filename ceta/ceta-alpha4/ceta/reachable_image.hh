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
#ifndef _reachable_image_hh_
#define _reachable_image_hh_

#include "ta.hh"

namespace ceta {
  /**
   * Stores the reachable states intersected with the a subset of the
   * states.
   */
  class reachable_image_t {
  public:
    typedef std::pair<std::set<state_t>, term_t> reachable_t;
    typedef std::vector<reachable_t> set_vector_t;
    typedef set_vector_t::const_iterator iterator;

    reachable_image_t(const std::set<state_t>& allowed_states)
      : allowed_states_(allowed_states) {
    }

    bool add(const std::set<state_t>& states, const term_t& term) {
      // Compute intersection of set and allowed_states.
      std::set<state_t> subset;
      std::set_intersection(
              allowed_states_.begin(), allowed_states_.end(),
              states.begin(), states.end(),
              std::inserter(subset, subset.begin()));
      bool result = set_image_.insert(subset).second;
      if (result)
        set_vector_.push_back(reachable_t(subset, term));
      return result;
    }

    const std::set<state_t>& states() const {
      return allowed_states_;
    }

    iterator begin() const {
      return set_vector_.begin();
    }

    iterator end() const {
      return set_vector_.end();
    }
  private:
    /** The set of states that are allowed to be in a reachable set. */
    std::set<state_t> allowed_states_;
    /**
     * The set of sets of states that are known to be reachable
     * intersected with the states in rule_states.
     */
    std::set< std::set<state_t> > set_image_;
    /**
     * The known states and the term used to reach the known states
     * stored in the order it was added.
     */
    set_vector_t set_vector_;
  };

  /**
   * Returns number of state sets added to image.
   * \relates reachable_image_t
   */
  inline
  size_t state_count(const reachable_image_t& image) {
    return std::distance(image.begin(), image.end());
  }

  /**
   * Returns last term and set added to image.
   * \relates reachable_image_t
   */
  inline
  const std::pair<std::set<state_t>, term_t>&
          back(const reachable_image_t& image) {
    reachable_image_t::iterator i = image.end();
    --i;
    return *i;
  }
}

#endif
