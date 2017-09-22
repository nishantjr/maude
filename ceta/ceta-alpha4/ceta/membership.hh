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
#ifndef membership_hh_
#define membership_hh_

#include <ceta/export.h>
#include <ceta/ta.hh>

/** Namespace for all of Ceta's declarations. */
namespace ceta {

/**
 * Returns complete set of states that the term reaches in the tree
 * automaton.
 */
const std::set<state_t>
reachable_states(const ta_t& ta, const term_t& term) CETA_DSO_EXPORT;

/**
 * Returns true if the term is in the language accepted by the tree
 * automaton.
 */
bool test_membership(const ta_t& ta, const term_t& term) CETA_DSO_EXPORT;

}


#endif
