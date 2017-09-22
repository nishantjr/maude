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
#ifndef _writer_hh_
#define _writer_hh_
/** \file
 * Utility for writing a range of objects to an output stream.
 */

#include <ostream>
#include <string>

namespace ceta {
  /**
   * A serializable object capable of writing a sequence of elements
   * into an <code>ostream</code>.  The template argument
   * <code>I</code> is the type of iterator used to mark the bounds
   * of the range.  The template argument <code>S</code> is the type
   * used as the spacer object.
   */
  template <typename I, typename S = std::string>
  class range_writer {
  public:
    /** 
     * Constructs a new range_writer for the range <code>[begin end)</code>
     * that uses <code>spacer</code> for separating elements.
     */
    range_writer(I begin, I end, const S& spacer) 
      : begin_(begin),
        end_(end),
        spacer_(spacer) {
    }
  
    /** Returns the iterator that marks the start of the range. */
    const I begin(void) const { return begin_; }
    /** Returns the iterator that marks the end of the range. */
    const I end(void) const { return end_; };
    
    /** 
     * Returns the element used to separate each object from the others
     * when written.
     */
    const S& spacer(void) const {
      return spacer_;
    }
  private:
    I begin_;
    I end_;
    S spacer_;
  };
  
  /**
   * Creates a range writer for the range [begin end) with each element
   * separated by a single space.
   */
  template <typename I>
  range_writer<I>
  make_range_writer(I begin, I end) {
    return range_writer<I,std::string>(begin, end, " ");
  }
  
  /** 
   * Writes each element in the range to the stream with the range's
   * spacer written between each element.
   * \relates range_writer
   */
  template <typename I, typename S>
  std::ostream& operator<<(std::ostream& o, const range_writer<I, S>& w) {
    I i(w.begin());
    if (i != w.end()) {
      o << *i;
      ++i;
      while (i != w.end()) {
        o << w.spacer() << *i;
        ++i;
      }
    }
    return o;
  }
}

#endif
