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
#ifndef _ldsolver_hh_
#define _ldsolver_hh_
/** \file
 * An incremental solver for computing the Hilbert basis of a system of
 * linear Diophantine equations.
 * The solver is based on the incremental algorithm in Contejean-Devie 94
 * with some additional enhancements to directly solve for an exact solution
 * when the unfrozen columns become linearly independent.
 */

#include <cstddef>
#include <vector>

#include "export.h"

namespace ceta {

  struct ld_solver_impl;

  /**
   * An incremental solver capable of computing the complete Hilbert basis
   * for the solutions to a system of linear Diophantine equations.  
   * The coefficient matrix A must be provided when the solver is
   * constructed, and <code>next</code> will successively new return minimal
   * non-zero solutions to Ax = 0.  To compute inhomongeneous solutions,
   * one may call <code>solve</code> with a vector v, then <code>next</code>
   * will return minimal solutions to Ax = v.
   */
  class ld_solver_t {
  public:

    /**
     * Construct an ld_solver for a coefficient matrix stored in column 
     * major order.
     */
    ld_solver_t(size_t nr, size_t nc, const int* coef);
    ~ld_solver_t();


    /** Returns the number of rows in the coefficient matrix. */
    size_t nr(void) const;
    /** Returns the number of columns in the coefficient matrix. */
    size_t nc(void) const;

    /** Start computing minimal solutions for a vector v. */
    void solve(const int* v);

    /** 
     * Returns the next solution or <code>NULL</code> if there are no more
     * solutions.
     */
    const bool next(std::vector<unsigned>& sol);
  private:
    // Disable copy construction and assignment.
    ld_solver_t(const ld_solver_t&);
    ld_solver_t& operator=(const ld_solver_t&);

    ld_solver_impl* solver_;
  };
}
#endif
