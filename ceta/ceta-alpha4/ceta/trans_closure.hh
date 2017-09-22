/* Copyright 2006-2007 University of Illinois at Urbana-Champaign
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
#ifndef _trans_closure_hh_
#define _trans_closure_hh_

/** \file
 * \brief Provides simple transitive-closure related algorithms.
 */

#include <map>
#include <set>
#include <vector>


namespace ceta {

/**
 * Helper function that closures set under transitivity, by examing all out
 * edges of elements of stack.
 */
template<typename E>
void transitive_closure_impl(const std::map<E, std::set<E> >& edge_map,
                             std::set<E>& set,
                             std::vector<E>& stack) {
  while (!stack.empty()) {
    typedef typename std::map<E, std::set<E> >::const_iterator map_iter;
    map_iter iedges = edge_map.find(stack.back());
    stack.pop_back();
    if (iedges == edge_map.end()) continue;
    const std::set<E>& edge_set = iedges->second;
    typedef typename std::set<E>::const_iterator set_iter;
    for (set_iter i = edge_set.begin(); i != edge_set.end(); ++i) {
      bool added = set.insert(*i).second;
      if (added) stack.push_back(*i);
    }
  }
}

/**
 * Adds e to set and all elements reachable from e to set.  This function
 * assumes that if set contains an element e', then everything reachable from
 * e' is in set.
 */
template<typename E>
void add_and_close(const std::map<E, std::set<E> >& edge_map,
                   std::set<E>& set,
                   const E& e) {
  typedef typename std::map<E, std::set<E> >::const_iterator map_iter;
  bool added = set.insert(e).second;
  if (added) {
    std::vector<E> stack;
    stack.push_back(e);
    transitive_closure_impl(edge_map, set, stack);
  }
}

/**
 * Closes set under transitivity with edges in map.
 */
template<typename E>
void transitive_closure(const std::map<E, std::set<E> >& edge_map,
                        std::set<E>& set) {
  std::vector<E> stack(set.begin(), set.end());
  transitive_closure_impl(edge_map, set, stack);
}

}
#endif


