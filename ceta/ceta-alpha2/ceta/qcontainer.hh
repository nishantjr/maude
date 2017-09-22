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
#ifndef _queue_hh_
#define _queue_hh_

#include <deque>
#include <ostream>
#include <utility>

namespace ceta {
namespace impl {
  /**
   * A container that queues up new elements in the order they are added.
   * The container type may be a set or map.
   */
  template<typename Container>
  class qcontainer_t {
  public:
    typedef typename Container::key_type key_type;
    typedef typename Container::value_type value_type;
    typedef typename Container::iterator iterator;
    typedef typename Container::const_iterator const_iterator;

    /** Returns underlying container. */
    const Container& container(void) const {
      return container_;
    }

    /** Returns 1 if element is in container and 0 otherwise. */
    size_t count(const key_type& elt) const {
      return container_.count(elt);
    }

    /** Inserts element into set. */
    void insert(const value_type& elt) {
      std::pair<iterator, bool> result = container_.insert(elt);
      if (result.second) {
        try {
          queue_.push_back(result.first);
        } catch (...) {
          container_.erase(result.first);
          throw;
        }
      }
    }

    /** Returns true if there queue is empty. */
    bool queue_empty(void) const {
      return queue_.empty();
    }

    /** Returns the first element in the queue. */
    const value_type& front(void) const {
      return *queue_.front();
    }

    /** Pops first element from queue. */
    void pop_front(void) {
      queue_.pop_front();
    }
  private:
    /** Set of reachables added so far. */
    Container container_;
    /** Queue of reachables not yet poped. */
    std::deque<iterator> queue_;
  };
}}
#endif
