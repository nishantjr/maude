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
#ifndef _op_explorer_hh_
#define _op_explorer_hh_

#include "ta.hh"
#include "reachable_sets.hh"

namespace ceta {

/** Abstract base reachable set explorer for an operator. */
class op_explorer_t {
public:
  op_explorer_t(void) {
  }

  virtual ~op_explorer_t() {
  }

  /** Adds reachable state to op explorer. */
  virtual
  void add_reachable(const std::set<state_t>& set,
                     const term_t& term) = 0;

  /** Explore from current states. */
  virtual void explore(reachable_sets_t& reachables) = 0;

  /** Returns true if this explorer has completely explored states. */
  virtual bool is_complete(void) const = 0;
private:
  // Disable copy construction and assignment.
  op_explorer_t(const op_explorer_t&);
  op_explorer_t& operator=(const op_explorer_t&);
};
}

#endif
