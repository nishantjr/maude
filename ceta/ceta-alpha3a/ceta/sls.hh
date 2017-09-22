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
#ifndef _sls_hh_
#define _sls_hh_
/** \file
 * Defines classes for representing semilinear sets and combining them with
 * boolean operations.
 */

#include <set>
#include <vector>

#include "export.h"

namespace ceta {
  struct lsg_impl;
  
  /** 
   * A collection of linear sets which share the same period.
   * A linear_set_group contains two sets of vectors: one for the constants
   * and the other for the periods.  We can often more efficiently perform
   * operations on semilinear sets by grouping the linear sets that compose
   * it in this way.
   */
  class linear_set_group {
  public:
    /** Container type for constants and periods */
    typedef std::set< std::vector<unsigned> > element_container;
    /** Iterator type for iterating over constants and periods. */
    typedef element_container::const_iterator iterator;
  
    /** 
     * Constructs an empty linear set group in the provided number of
     * dimensions.
     */
    explicit linear_set_group(size_t dim = 0);

    /** Constructs a copy of a linear set group. */
    linear_set_group(const linear_set_group& o);
    /** Assigns a linear set group to this group. */
    linear_set_group& operator=(const linear_set_group& o);

    ~linear_set_group();
  
    /** Returns number of dimensions of this group. */
    size_t dim(void) const;
  
    /** Returns the constants of this group. */
    const element_container& constants(void) const;
    /** Returns the periods of this group. */
    const element_container& periods(void) const;
  
    /** 
     * Inserts a new constant.
     * \param constant Pointer to array with values of constant.
     */
    void insert_constant(const unsigned* constant);
  
    /**
     * Inserts a new period.
     * \param period Pointer to array with values of period.
     */
    void insert_period(const unsigned* period);

    /**
     * Returns true if element can be reached from a constant in this group
     * by adding zero or more periods.
     */
    bool member(const unsigned* ele) const;

    /**
     * Removes constants that are elements of the group even if they are
     * removed.
     */
    void compact_constants(void);
  private:
    lsg_impl* impl_;
  };

  /**
   * Writes the constants and periods to the ostream.
   * \relates linear_set_group
   */
  std::ostream& operator<<(std::ostream& o, const ceta::linear_set_group& g);
  
  /**
   * Returns the linear set group containing elements in both linear set
   * groups.
   * \relates linear_set_group
   */
  linear_set_group intersect(const linear_set_group& x,
                             const linear_set_group& y);
  
  /** Defines a total order of linear_set_groups based on the periods. */
  class strict_period_order {
  public:
    /** 
     * Returns true if the periods in x are strictly less than the periods
     * in y.
     */
    bool operator()(const linear_set_group& x, const linear_set_group& y) {
      return x.periods() < y.periods();
    }
  };
  
  struct sls_impl;
  
  /** A semilinear set representation. */
  class semilinear_set {
    typedef std::set<linear_set_group, strict_period_order> container;
  public:
    /** 
     * Iterator type to enumerate the linear set groups that compose the
     * semilinear set.
     */
    typedef container::const_iterator iterator;

    /** Constructs an empty semilinear set in the specified dimension. */
    semilinear_set(size_t dim = 0);
    /** Constructs a copy of a semilinear set. */
    semilinear_set(const semilinear_set& o);
    ~semilinear_set();
  
    /** Assigns a semilinear set to this set. */
    semilinear_set& operator=(const semilinear_set& o);
  
    /** Returns number of dimensions of this set. */
    size_t dim(void) const;

    /** Returns an iterator to the first group of this set. */
    iterator begin(void) const;

    /** Returns an iterator marking the end of the groups in this set. */
    iterator end(void) const;
    
    /** Inserts a linear set group into this set. */
    void insert(const linear_set_group& group);
  private:
    sls_impl* impl_;
  };
  /**
   * Writes the semilinear set to the ostream.
   * \relates semilinear_set
   */
  std::ostream& operator<<(std::ostream& o, const ceta::semilinear_set& s);
  
  /**
   * Returns a semilinear set containing all vectors in a dimension whose
   * 1-norm is at least the provided minimum size.
   * \relates semilinear_set
   */
  semilinear_set min_size_set(size_t dim, size_t min_size);

  /** 
   * Returns a set containing the all the vectors of natural numbers of the
   * specified dimension.
   * \relates semilinear_set
   */
  semilinear_set complete_set(size_t dim);

  /**
   * Returns the complement of a semilinear set.
   * \relates semilinear_set
   */
  semilinear_set complement(const semilinear_set& set);

  /**
   * Returns a semilinear set containing the same elements as the provided
   * set, but where the periods of every group composing the set are linearly
   * independent.
   * \relates semilinear_set
   */
  semilinear_set independent_periods(const semilinear_set& set);

  /**
   * Returns the intersection of two semilinear sets.
   * \relates semilinear_set
   */
  semilinear_set intersect(const semilinear_set& x, const semilinear_set& y);

  /**
   * Returns true if the semilinear set is empty.
   * \relates semilinear_set
   */
  bool is_empty(const semilinear_set& set);

  /**
   * Returns true if the element e is in the semilinear set.
   */
  bool member(const unsigned* e, const semilinear_set& set);
}

#endif
