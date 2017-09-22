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
#ifndef _counter_automata_hh_
#define _counter_automata_hh_

#include "op_explorer.hh"
#include "closure.hh"

namespace ceta {
class counter_ac_impl_t;

class counter_ac_explorer_t : public op_explorer_t {
public:
  counter_ac_explorer_t(const theory_t& theory,
                        const op_t& op,
                        const closure_t& closure,
                        const std::vector<rule_t>& rules);
  void add_reachable(const std::set<state_t>& states, const term_t& term);

  void explore(reachable_sets_t& reachables);
  bool is_complete(void) const;
private:
  //Disable copy construction and assignment
  counter_ac_explorer_t(const counter_ac_explorer_t&);
  counter_ac_explorer_t& operator=(const counter_ac_explorer_t&);

  boost::shared_ptr<counter_ac_impl_t> impl_;
};
}

#endif
