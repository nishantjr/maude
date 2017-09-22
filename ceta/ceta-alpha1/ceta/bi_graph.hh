/* Copyright 2005 Joe Hendrix
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
#ifndef _bi_graph_hh_
#define _bi_graph_hh_
#include <map>
#include <set>

namespace ceta {
  /**
   * A generic bi-partite directed graph where the vertices in each
   * paritition may have different types.
   */
  template<class Lhs, class Rhs>
  class bi_graph_t {
  public:
    typedef std::map<Lhs, std::set<Rhs> > child_graph_t;
    typedef std::map<Rhs, std::set<Lhs> > parent_graph_t;

    /** Returns true if graph contains an edge lhs -> rhs. */
    bool contains(Lhs lhs, Rhs rhs) const {
      child_iter i = children_.find(lhs);
      return (i != children_.end()) && (i->second.count(rhs) > 0);
    }

    /**
     * Adds edge lhs -> rhs to graph returning true if there was no
     * such edge already in the graph.
     */
    bool insert(Lhs lhs, Rhs rhs) {
      if (contains(lhs, rhs))
        return false;
      std::set<Rhs>& lhs_c = children_[lhs];
      lhs_c.insert(rhs);
      try {
        parents_[rhs].insert(lhs);
      } catch (...) {
        lhs_c.erase(rhs);
        throw;
      }
      return true;
    }

    /** Erases the edge from lhs to rhs in the graph. */
    void erase(Lhs lhs, Rhs rhs) {
      typename child_graph_t::iterator ic = children_.find(lhs);

      if (ic != children_.end())
        ic->second.erase(rhs);

      typename parent_graph_t::iterator ip = parents_.find(rhs);
      if (ip != parents_.end())
        ip->second.erase(lhs);
    }

    /** Returns all the vertices reachable from lhs. */
    const std::set<Rhs>& children(Lhs lhs) const {
      child_iter i = children_.find(lhs);
      if (i != children_.end()) {
        return i->second;
      } else {
        static std::set<Rhs> empty_set;
        return empty_set;
      }
    }

    /** Returns all the vertices with can reach rhs. */
    const std::set<Lhs>& parents(Rhs rhs) const {
      parent_iter i = parents_.find(rhs);
      if (i != parents_.end()) {
        return i->second;
      } else {
        static std::set<Lhs> empty_set;
        return empty_set;
      }
    }
  private:
    typedef typename child_graph_t::const_iterator child_iter;
    typedef typename parent_graph_t::const_iterator parent_iter;
    /** Map containing edges lhs -> rhs. */
    child_graph_t children_;
    /** Map containing reversed edges rhs -> lhs. */
    parent_graph_t parents_;
  };
}
#endif
