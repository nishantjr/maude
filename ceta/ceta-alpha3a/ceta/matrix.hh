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
#ifndef _matrix_hh_
#define _matrix_hh_
/** \file
 * Data structures and algorithms for manipulating matrices.
 */

#include <iterator>
#include <vector>

namespace ceta {
  /**
   * Adds a vector a*x to a vector y.
   *
   * @param a       Value to scale x by when adding.
   * @param x_begin Start of vector x.
   * @param x_end   End of vector x.
   * @param y_begin Start of vector y.
   */
  template<typename T, typename I, typename O>
  void axpy(const T& a, I x_begin, I x_end, O y_begin) {
    O y = y_begin;
    for (I x = x_begin; x != x_end; ++x) {
      *y += a * *x;
      ++y;
    }
  }

  /**
   * Scale vector by a factor.
   *
   * @param a       Value to scale vector by.
   * @param x_begin Start of vector.
   * @param x_end   End of vector.
   */
  template<typename T, typename I>
  void scal(const T& a, I x_begin, I x_end) {
    for (I x = x_begin; x != x_end; ++x)
      *x *= a;
  }

  /**
   * Returns dot product of two vectors.
   *
   * @param x_begin Start of first vector.
   * @param x_end   End of first vector.
   * @param y_begin Start of second vector.
   */
  template<typename I, typename J>
  typename std::iterator_traits<I>::value_type
  dot_product(I x_begin, I x_end, J y_begin) {
    typename std::iterator_traits<I>::value_type result = 0;
    J y = y_begin;
    for (I x = x_begin; x != x_end; ++x) {
      result += *x * *y;
      ++y;
    }
    return result;
  }

  /**
   * A view of an array that exposes elements as a matrix in row-major
   * order.
   */
  template<typename T>
  class row_matrix_view {
  public:
    typedef T value_type;
    typedef T& reference;
    typedef const T& const_reference;
    /** Modifiable type returned by row() that may be treated as an array. */
    typedef T* row_type;
    /** Const type returned by row() that may be treated as an array. */
    typedef const T* const_row_type;

    /** Constructs a new row matrix view. */
    row_matrix_view(size_t nr, size_t nc, T* elts)
      : nr_(nr),
        nc_(nc),
        elts_(elts) {
    }

    /** Returns number of rows in matrix. */
    size_t nr(void) const {
      return nr_;
    }

    /** Returns number of columns in matrix. */
    size_t nc(void) const {
      return nc_;
    }

    const_reference operator()(size_t r, size_t c) const {
      return elts_[r * nc_ + c];
    }

    const_reference operator()(size_t r, size_t c) {
      return elts_[r * nc_ + c];
    }

    row_type row(size_t r) {
      return elts_ + r * nc_;
    }

    const_row_type row(size_t r) const {
      return elts_ + r * nc_;
    }
  private:
    const size_t nr_;
    const size_t nc_;
    T* elts_;
  };

  /**
   * A helper method that allows constructing a row_matrix_view without
   * naming the element type explicitly.
   * \relates row_matrix_view
   */
  template<typename T>
  row_matrix_view<T>
  make_row_matrix_view(size_t nr, size_t nc, T* elts) {
    return row_matrix_view<T>(nr, nc, elts);
  }

  /**
   * A view of an array that exposes elements as a matrix in column-major
   * order.
   */
  template<typename T>
  class col_matrix_view {
  public:
    typedef T value_type;
    typedef T& reference;
    typedef const T& const_reference;

    col_matrix_view(size_t nr, size_t nc, T* elts)
      : nr_(nr),
        elts_(elts) {
    }

    const_reference operator()(size_t r, size_t c) const {
      return elts_[c * nr_ + r];
    }

    reference operator()(size_t r, size_t c) {
      return elts_[c * nr_ + r];
    }

    const T* col(size_t c) const {
      return elts_ + c * nr_;
    }

    T* col(size_t c) {
      return elts_ + c * nr_;
    }
  private:
    size_t nr_;
    T* elts_;
  };

  /**
   * A helper method that allows constructing a col_matrix_view without
   * naming the element type explicitly.
   * \relates col_matrix_view
   */
  template<typename T>
  col_matrix_view<T>
  make_col_matrix_view(size_t nr, size_t nc, T* elts) {
    return col_matrix_view<T>(nr, nc, elts);
  }

  /** A view of matrix with the columns permuted into a different order. */
  template<typename M>
  class col_permutation_matrix_view {
  public:
    typedef typename M::value_type value_type;
    typedef typename M::reference reference;
    typedef typename M::const_reference const_reference;

    col_permutation_matrix_view(const M& m, const size_t* col_map)
      : m_(m),
        col_map_(col_map) {
    }

    const_reference operator()(size_t r, size_t c) const {
      return m_(r, col_map_[c]);
    }
  private:
    const M& m_;
    const size_t* col_map_;
  };

  template<typename M>
  col_permutation_matrix_view<M>
  make_col_permutation_matrix_view(const M& m, const size_t* col_map) {
    return col_permutation_matrix_view<M>(m, col_map);
  }


  /** Resizable matrix for which rows may be retrieved as vectors. */
  template<typename T>
  class row_matrix {
  public:
    typedef T value_type;
    typedef std::vector<T> row_type;
    typedef typename row_type::reference reference;
    typedef typename row_type::const_reference const_reference;

    /** Construct a row matrix with nr = nc = 0. */
    row_matrix(void)
      : nr_(0),
        nc_(0),
        vals_(0) {
    }

    /** Construct a matrix given an row major array of element values. */
    row_matrix(size_t nr, size_t nc, const T* vals)
      : nr_(nr),
        nc_(nc),
        vals_(nr) {
      typedef typename storage_type::iterator iter;
      for (iter i = vals_.begin(); i != vals_.end(); ++i) {
        const T* vals_end = vals + nc;
        i->insert(i->end(), vals, vals_end);
        vals = vals_end;
      }
    }

    size_t nr() const {
      return nr_;
    }

    size_t nc() const {
      return nc_;
    }

    void resize(size_t nr, size_t nc, const T& initial_value) {
      // If adding rows
      if (nr > nr_) {
        vals_.resize(nr_);
        vals_.resize(nr);
      }
      for (size_t i = 0; i != nr; ++i) {
        row_type& cur_row = vals_[i];
        // In case the cur_row is larger than nc_, we initially resize to
        // nc_ to discard previous values.
        cur_row.resize(nc_, initial_value);
        cur_row.resize(nc, initial_value);
      }
      // To remove rows
      vals_.resize(nr);
      nr_ = nr;
      nc_ = nc;
    }

    row_type& row(size_t r) {
      return vals_[r];
    }

    const row_type& row(size_t r) const {
      return vals_[r];
    }

    reference operator()(size_t r, size_t c) {
      return row(r)[c];
    }

    const_reference operator()(size_t r, size_t c) const {
      return row(r)[c];
    }
  private:
    typedef std::vector< row_type > storage_type;
    size_t nr_;
    size_t nc_;
    /** Elements of matrix stored in column major order. */
    storage_type vals_;
  };

  /** Resizable matrix for which columns may be retrieved as vectors. */
  template<typename T>
  class col_matrix {
  public:
    typedef T value_type;
    typedef typename row_matrix<T>::row_type col_type;
    typedef typename row_matrix<T>::reference reference;
    typedef typename row_matrix<T>::const_reference const_reference;

    col_matrix(void)
      : m_() {
    }

    /** Construct a matrix given an column major array of element values. */
    col_matrix(size_t nr, size_t nc, const T* vals)
      : m_(nc, nr, vals) {
    }

    size_t nr() const {
      return m_.nc();
    }

    size_t nc() const {
      return m_.nr();
    }

    void resize(size_t nr, size_t nc, const T& initial_value) {
      m_.resize(nc, nr, initial_value);
    }

    col_type& col(size_t c) {
      return m_.row(c);
    }

    const col_type& col(size_t c) const {
      return m_.row(c);
    }

    reference operator()(size_t r, size_t c) {
      return col(c)[r];
    }

    const_reference operator()(size_t r, size_t c) const {
      return col(c)[r];
    }
  private:
    row_matrix<T> m_;
  };

  // Initializes matrix to be diagonal matrix where every entry
  // along the diagonal equals val.
  template<typename M, typename V>
  void fill_identity_matrix(size_t n, M m, V val) {
    for (size_t c(0); c != n; ++c) {
      for (size_t r(0); r != c; ++r)
        m(r, c) = 0;
      m(c, c) = val;
      for (size_t r(c + 1); r != n; ++r)
        m(r, c) = 0;
    }
  }


  template<typename T>
  class LU {
  public:
    template<typename F>
    LU(size_t nr, size_t nc, const F& valfn);

    ~LU() {
      delete [] row_idx_;
      delete [] zero_fns_;
    }

    size_t nr() const {
      return nr_;
    }

    size_t nc() const {
      return nc_;
    }

    size_t rank() const {
      return rank_;
    }

    /**
     * \brief Returns the dot product of [val ... val + nr) and row r
     */
    T row_dot_product(const T* val, const T* val_end, size_t r) const {
      typedef typename std::vector<T>::const_iterator iter;

      T result = 0;
      if (val != val_end) {
        iter irow = vals_.begin() + r;
        result += *val * *irow;
        ++val;
        while (val != val_end) {
          irow += nr_;
          result += *val * *irow;
          ++val;
        }
      }
      return result;
    }

    bool solve(const int* b, T* s) const {
      // Forward substitution
      T l[rank_];
      for (size_t c = 0; c != rank_; ++c) {
        l[c] = T(b[row_idx_[c]]);
        l[c] -= row_dot_product(l, l + c, c);
      }

      // Iterate through rows below maximum rank
      for (size_t r = rank_; r != nr_; ++r) {
        // Return false if remaining rows do not balance
        T expected_value = row_dot_product(l, l + rank_, r);
        if (expected_value != T(b[row_idx_[r]]))
          return false;
      }

      // Back substitution - note that since we are iterating backwards, we
      // must be careful c does not wrap around.
      for (size_t c = rank_; c > 0;) {
        --c;
        s[c] = l[c] / vals_[c * (nr_ + 1)];
        axpy(-s[c], &vals_[c * nr_], &vals_[c * (nr_ + 1)], l);
      }

      return true;
    }


    const T* zero_fn(size_t i) const { return zero_fns_ + i * nc_; }

    /** Returns determinate of matrix */
    T det(void) const {
      // If matrix does not have full rank, return 0
      if ((rank_ < nr_) || (rank_ < nc_))
        return 0;

      // Compute determinate of upper matrix.
      T result(1);
      for (size_t i(0); i != rank_; ++i)
        result *= vals_[i * (nr_ + 1)];
      return result;
    }

    const size_t* row_idx(void) const { return row_idx_; };
  private:
    LU(const LU&);
    LU& operator=(const LU&);

    const size_t nr_;
    const size_t nc_;

    // rank_ of matrix
    size_t rank_;

    // Column-major matrix for storing lower and upper matrices.  Contains
    // nr_ rows and rank_ columns.
    std::vector<T> vals_;

    // Array for storing row pivot information.  If row_idx_[i] = j,
    // then row j in the original matrix is now stored at row i.
    size_t* row_idx_;

    // Row-major Matrix for storing zerofns.  There are nc_ - rank_ rows
    // and each row contains nc_ entries.
    T* zero_fns_;
  };

  template<typename T>
  template<typename F>
  LU<T>::LU(size_t nr, size_t nc, const F& valfn)
    : nr_(nr),
      nc_(nc),
      rank_(0),
      row_idx_(NULL),
      zero_fns_(NULL) {
    try {
      // contains lu matrix in column major order
      T lu_elts[nr*nc];
      col_matrix_view<T> lu(nr, nc, lu_elts);

      // Contains weighting of each unfrozen column
      T fns[nc * nc];

      // Initialize row_idx_ with natural row order
      row_idx_ = new size_t[nr];
      for (size_t r = 0; r != nr; ++r)
        row_idx_[r] = r;

      // Initialize fns to be diagonal matrix
      for (size_t c(0); c < nc; ++c)
        for (size_t r(0); r < nc; ++r)
          fns[c * nc + r] = (r == c) ? T(1) : T(0);

      size_t zero_start[nc];
      size_t* zero_end(zero_start);

      size_t nonzero_start[nc];
      size_t* nonzero_end(nonzero_start);

      for (size_t c(0); c != nc; ++c) {
        // Copy values of column into lu
        for (size_t r = 0; r != nr_; ++r) {
          lu(r, rank_) = valfn(row_idx_[r], c);
        }

        T* curcol = lu.col(rank_);

        // Apply reductions from previous columns
        for (size_t pc(0); pc != rank_; ++pc) {
          T* prevcol = lu.col(pc);
          axpy(-curcol[pc],
               // from lu[pc + 1, pc]
               prevcol + pc + 1,
               // to end of column
               prevcol + nr,
               // curcol[pc + 1] ...
               curcol + pc + 1);
          axpy(-curcol[pc ],
               // from  fns[pc]
               fns + pc * nc,
               // to end of equation
               fns + (pc + 1) * nc,
               fns + c * nc);
        }

        // Find pivot row for this matrix
        size_t pivot_idx(rank_);
        while ((pivot_idx != nr_) && (curcol[pivot_idx] == T(0)))
          ++pivot_idx;

        // Pivot rows
        if (pivot_idx != nr_) {
          if (pivot_idx != rank_) {
            std::swap(row_idx_[pivot_idx], row_idx_[rank_]);

            for (size_t c(0); c <= rank_; ++c)
  	    std::swap(lu(pivot_idx, c), lu(rank_, c));
          }
          T row_mult = T(1) / curcol[rank_];
          scal(row_mult, curcol + rank_ + 1, curcol + nr_);
          scal(row_mult, fns + c * nc, fns + (c + 1) * nc);
          ++rank_;
          *(nonzero_end++) = c;
        } else {
          // Column was all zeros so do not pivot
          *(zero_end++) = c;
        }
      }

      // Copy zero_fns
      zero_fns_ = new T[(nc - rank_) * nc];
      for (size_t iFn(0); iFn != nc_ - rank_; ++iFn) {
        std::copy(fns + zero_start[iFn] * nc,
                  fns + (zero_start[iFn] + 1) * nc,
                  zero_fns_ + iFn * nc_);
      }

      // Contruct vals_ array and copy values into it from lu
      vals_.resize(rank_ * nr_);
      std::copy(lu_elts, lu_elts + rank_ * nr_, vals_.begin());

  #ifdef RUNTIME_MONITORING
      // Check LU Mult
      for (size_t c(0); c != rank_; ++c) {
        for (size_t r(0); r != nr_; ++r) {
          // Compute dot product of row r of lower triangular matrix
          // and col c of upper triangular matrix
          T sum(0);

          for (size_t i = 0; i != std::min(c + 1, r + 1); ++i) {
            if (r == i) {
              sum += lu(i, c);
            } else {
    	    sum += lu(r, i) * lu(i, c);
            }
          }
          T expected(valfn(row_idx_[r], nonzero_start[c]));
          if (sum != expected) {
    	  exit(1);
          }
        }
      }
  #endif
    } catch (...) {
      delete [] row_idx_;
      delete [] zero_fns_;
      throw;
    }
  }

}
#endif
