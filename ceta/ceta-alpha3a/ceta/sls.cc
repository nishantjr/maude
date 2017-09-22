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
/** \file
 * Implementation of operations on semilinear sets.
 */
#include <algorithm>
#include <iterator>
#include <limits>
#include <map>
#include <numeric>
#include <set>
#include <stdexcept>

#include <boost/rational.hpp>

#include "sls.hh"
#include "ldsolver.hh"
#include "matrix.hh"
#include "writer.hh"


using namespace ceta;
using namespace std;
typedef boost::rational<long long> rational;

using boost::gcd;

namespace ceta {
  class lsg_impl {
  public:
    typedef std::set< std::vector<unsigned> > element_container;
    typedef element_container::const_iterator iterator;

    lsg_impl(size_t dim = 0)
      : dim_(dim),
        constants_(),
        periods_() {
    }

    /** Number of dimensions set is subset of */
    size_t dim(void) const {
      return dim_;
    }

    const element_container& constants() const {
      return constants_;
    }

    const element_container& periods() const {
      return periods_;
    }

    /** Inserts a new constant obtained from a ForwardIterator constant. */
    template<class I>
    void insert_constant(I constant) {
      constants_.insert(std::vector<unsigned>(constant, constant + dim_));
    }

    template<class I>
    void insert_period(I period) {
      bool add(false);
      I p_end(period + dim_);
      for (I ip(period); !add && (ip != p_end); ++ip)
        add = (*ip > 0);
      if (add)
        periods_.insert(std::vector<unsigned>(period, period + dim_));
    }

    bool member(const unsigned* e) const {
      return member(e, constants_.end());
    }


    void compact_constants(void) {
      iterator i(constants_.begin());
      while (i != constants_.end()) {
        const std::vector<unsigned>& v(*i);
        if (member(&v[0], i)) {
          iterator next(i);
          ++next;
          constants_.erase(i);
          i = next;
        } else {
          ++i;
        }
      }
    }
  private:
    bool member(const unsigned* ele, iterator ignored_constant) const {
      int coef[dim_ * periods_.size()];
      {
        int* icoef(coef);
        // Populate coef with periods
        for (iterator i(periods_.begin()); i != periods_.end(); ++i) {
          std::copy(i->begin(), i->end(), icoef);
          icoef += dim_;
        }
      }
      ld_solver_t s(dim_, periods_.size(), coef);

      vector<unsigned> sol(periods_.size());
      bool found(false);
      for (iterator ic(constants_.begin());
           !found && (ic != constants_.end());
           ++ic) {
        if (ic != ignored_constant) {
          // Compute difference of two constants
          int diff[dim_];
          for (size_t i(0); i != dim_; ++i)
            diff[i] = ele[i] - (*ic)[i];

          // Solve for diff
          s.solve(diff);
          found = s.next(sol);
        }
      }
      return found;
    }

    size_t dim_;
    element_container constants_;
    element_container periods_;
  };

  // linear_set_group member definitions.

  linear_set_group::linear_set_group(size_t dim)
    : impl_(new lsg_impl(dim)) {
  }

  linear_set_group::linear_set_group(const linear_set_group& o)
    : impl_(new lsg_impl(*o.impl_)) {
  }

  linear_set_group::~linear_set_group(void) {
    delete impl_;
  }

  linear_set_group& linear_set_group::operator=(const linear_set_group& o) {
    *impl_ = *o.impl_;
    return *this;
  }

  size_t linear_set_group::dim(void) const {
    return impl_->dim();
  }

  const linear_set_group::element_container&
  linear_set_group::constants(void) const {
    return impl_->constants();
  }

  const linear_set_group::element_container&
  linear_set_group::periods(void) const {
    return impl_->periods();
  }

  void linear_set_group::insert_constant(const unsigned* constant) {
    impl_->insert_constant(constant);
  }

  void linear_set_group::insert_period(const unsigned* period) {
    impl_->insert_period(period);
  }

  void linear_set_group::compact_constants(void) {
    impl_->compact_constants();
  }

  bool linear_set_group::member(const unsigned* e) const {
    return impl_->member(e);
  }

  static
  void output_vector_list(std::ostream& o,
                          ceta::linear_set_group::iterator start,
                          ceta::linear_set_group::iterator end) {
    ceta::linear_set_group::iterator i(start);

    if (i != end) {
      o << make_range_writer(i->begin(), i->end());
      ++i;
      while (i != end) {
        o << ", " << make_range_writer(i->begin(), i->end());
        ++i;
      }
    }
  }

  std::ostream& operator<<(std::ostream& o, const linear_set_group& g) {
    o << "L(";
    output_vector_list(o, g.constants().begin(), g.constants().end());
    o << "; ";
    output_vector_list(o, g.periods().begin(), g.periods().end());
    o << ")";
    return o;
  }
}

namespace ceta {
namespace impl {
  static
  linear_set_group complete_set_group(size_t dim) {
    linear_set_group result(dim);
    unsigned v[dim];
    std::fill(v, v + dim, 0);
    // Add zero constant
    result.insert_constant(v);
    // Add periods e_1 e_2 ... e_dim
    for (unsigned* iv(v); iv != v + dim; ++iv) {
      *iv = 1;
      result.insert_period(v);
      *iv = 0;
    }
    return result;
  }

  class constant_insert_iterator {
  public:
    typedef std::output_iterator_tag iterator_category;
    typedef unsigned* value_type;

    explicit constant_insert_iterator(linear_set_group& g) : g_(g) {};
    constant_insert_iterator& operator++(void) { return *this; }
    constant_insert_iterator& operator++(int ) { return *this; }
    constant_insert_iterator& operator*(void) { return *this; }

    constant_insert_iterator& operator=(unsigned* i) {
      g_.insert_constant(i);
      return *this;
    }
  private:
    linear_set_group& g_;
  };

  template<class I>
  class period_insert_iterator {
  public:
    typedef std::output_iterator_tag iterator_category;
    typedef I value_type;
    typedef I& reference;
    typedef I* pointer;
    typedef ptrdiff_t difference_type;

    explicit period_insert_iterator(linear_set_group& g)
      : g_(g) {
    };
    period_insert_iterator& operator++(void) { return *this; }
    period_insert_iterator& operator++(int ) { return *this; }
    period_insert_iterator& operator*(void) { return *this; }

    period_insert_iterator& operator=(I i) {
      g_.insert_period(i);
      return *this;
    }
  private:
    linear_set_group& g_;
  };

  /**
   * An OutputIterator that applies a linear transformation to input before
   * forwarding it to another OutputIterator.
   */
  template<class R, class M, class O>
  class linear_transform {
  public:
    linear_transform(size_t nr, size_t nc, const R* c, const M& m, O o)
      : nr_(nr), nc_(nc), c_(c), m_(m), o_(o) {}

    linear_transform operator++(void) { ++o_; return *this; }
    linear_transform operator*(void) { return *this; };

    template<class I>
    linear_transform operator=(const I* x) {
      R r[nr_];
      std::copy(c_, c_ + nr_, r);
      for (size_t ir(0); ir != nr_; ++ir) {
        for (size_t ic(0); ic != nc_; ++ic)
          r[ir] += m_(ir, ic) * x[ic];
      }
      *o_ = r;
      return *this;
    }
  private:
    size_t nr_;
    size_t nc_;
    const R* c_;
    const M& m_;
    O o_;
  };

  template<typename R, typename M, typename O>
  static
  linear_transform<R, M, O>
  make_linear_transform(size_t nr, size_t nc, const R* c, const M& m, O o) {
    return linear_transform<R, M, O>(nr, nc, c, m, o);
  }

  /**
   * Writes each element of each period in the group to output.
   */
  template<bool Pos, typename O>
  static
  void copy_periods(const linear_set_group& g, O output) {
    for (linear_set_group::iterator i(g.periods().begin());
         i != g.periods().end();
         ++i) {
      if (Pos) {
        std::copy(i->begin(), i->end(), output);
      } else {
        std::transform(i->begin(), i->end(), output, std::negate<int>());
      }
      output += g.dim();
    }
  }

  /**
   * Copies a range [start ... end) of arrays of length n into an output
   * iterator.  The output iterator value_type constuctor with arguments
   * (*i, *i + n) is invoked.
   */
  template<typename V, typename I, typename O>
  static
  void copy_arrays(size_t n, I start, I end, O output) {

    for (I i(start); i != end; ++i) {
      *output = V(i->begin(), i->end());
      ++output;
    }
  }

  /**
   * retrieve_solutions repeatadly finds new solutions and assigns them
   * to o.  That is for each new solution s, retrieve_solutions calls
   * *o = s, and then ++o.  This continues until there all solutions
   * have been found.
   */
  template<class O>
  void retrieve_solutions(ld_solver_t& s, O o) {
    vector<unsigned> sol(s.nc());
    while (s.next(sol)) {
      *o = &sol[0];
      ++o;
    }
  }
}}

using namespace ceta::impl;

namespace ceta {
  linear_set_group
    intersect(const linear_set_group& x,
              const linear_set_group& y) {
    if (x.dim() != y.dim()) {
      throw logic_error("linear_set_group dimensions must be equal");
    }

    size_t dim(x.dim());

    size_t xnp(x.periods().size());
    size_t ynp(y.periods().size());

    int coef[dim * (xnp + ynp)];

    copy_periods<true>( x, coef);
    copy_periods<false>(y, coef + dim * xnp);

    ld_solver_t solver(dim, xnp + ynp, coef);

    linear_set_group result(dim);

    // All zero constant array
    unsigned zero_vector[dim];
    std::fill(zero_vector, zero_vector + dim, 0);

    retrieve_solutions(solver,
        make_linear_transform(dim, xnp, zero_vector,
            col_matrix_view<int>(x.dim(), xnp, coef),
            period_insert_iterator<const unsigned*>(result)));

    typedef linear_set_group::iterator iter;
    for (iter ix(x.constants().begin()); ix != x.constants().end(); ++ix) {
      for (iter iy(y.constants().begin()); iy != y.constants().end(); ++iy) {

        // Compute difference of two constants
        int diff[x.dim()];
        std::transform(iy->begin(), iy->end(),
                       ix->begin(),
                       diff, minus<int>());

        solver.solve(diff);
        retrieve_solutions(solver,
            make_linear_transform(dim, xnp, &(*ix)[0],
                col_matrix_view<int>(dim, xnp, coef),
                constant_insert_iterator(result)));
      }
    }
    return result;
  }

  class sls_impl {
    typedef std::set<linear_set_group, strict_period_order> container;
  public:
    typedef container::const_iterator iterator;

    sls_impl(size_t dim = 0)
      : dim_(dim),
        groups_() {
    }

    sls_impl(const sls_impl& o)
      : dim_(o.dim_),
        groups_(o.groups_) {
    }

    sls_impl& operator=(const sls_impl& o) {
      groups_ = o.groups_;
      dim_ = o.dim_;
      return *this;
    }

    size_t dim(void) const {
      return dim_;
    }

    iterator begin(void) const {
      return groups_.begin();
    }

    iterator end(void) const {
      return groups_.end();
    }

    void insert(const linear_set_group& group) {
      // If group is non-empty
      if (group.constants().empty() == false) {
        container::iterator i(groups_.find(group));
        if (i == groups_.end()) {
          linear_set_group copy(group);
          copy.compact_constants();
          groups_.insert(copy);
        } else {
          linear_set_group& original = const_cast<linear_set_group&>(*i);
          for (lsg_impl::iterator ic(group.constants().begin());
               ic != group.constants().end();
               ++ic) {
            original.insert_constant(&(*ic)[0]);
          }
          original.compact_constants();
        }
      }
    }
  private:
    size_t dim_;
    container groups_;
  };

  semilinear_set::semilinear_set(size_t dim)
    : impl_(new sls_impl(dim)) {
  }

  semilinear_set::semilinear_set(const semilinear_set& o)
    : impl_(new sls_impl(*o.impl_)) {
  }

  semilinear_set::~semilinear_set() {
    delete impl_;
  }

  semilinear_set& semilinear_set::operator=(const semilinear_set& o) {
    *impl_ = *o.impl_;
    return *this;
  }

  size_t semilinear_set::dim(void) const {
    return impl_->dim();
  }

  semilinear_set::iterator semilinear_set::begin(void) const {
    return impl_->begin();
  }

  semilinear_set::iterator semilinear_set::end(void) const {
    return impl_->end();
  }

  void semilinear_set::insert(const linear_set_group& group) {
    impl_->insert(group);
  }

  std::ostream& operator<<(std::ostream& o, const semilinear_set& s) {
    typedef ceta::semilinear_set::iterator iter;

    for (iter i = s.begin(); i != s.end(); ++i)
      o << *i << std::endl;
    return o;
  }

  bool member(const unsigned* e, const semilinear_set& set) {
    typedef semilinear_set::iterator iter;
    bool found(false);
    for (iter i(set.begin()); !found && (i != set.end()); ++i)
      found = i->member(e);
    return found;
  }

  semilinear_set
  intersect(const semilinear_set& x, const semilinear_set& y) {

    if (x.dim() != y.dim()) {
      throw logic_error("Semilinear dimensions must be equal.");
    }
    semilinear_set result(x.dim());
    for (semilinear_set::iterator ix(x.begin()); ix != x.end(); ++ix)
      for (semilinear_set::iterator iy(y.begin()); iy != y.end(); ++iy)
        result.insert(intersect(*ix, *iy));
    return result;
  }

  semilinear_set complete_set(size_t dim) {
    semilinear_set result(dim);
    result.insert(complete_set_group(dim));
    return result;
  }

  semilinear_set min_size_set(size_t dim, size_t min_size) {
    if (min_size == 0)
      return complete_set(dim);

    if (dim == 0)
      return semilinear_set(dim);

    semilinear_set result(dim);

    linear_set_group g(dim);
    // Add constants with minimum cardinality
    size_t stack[min_size];
    size_t i(0);
    stack[i] = 0;
    bool complete = false;
    unsigned con[dim];
    std::fill(con, con + dim, 0);
    while (!complete) {
      if (i == min_size) {
        g.insert_constant(con);
        --i;
        --con[stack[i]];
        ++stack[i];
      } else if (stack[i] == dim) {
        if (i == 0) {
          complete = true;
        } else {
          --i;
          --con[stack[i]];
          ++stack[i];
        }
      } else {
        ++con[stack[i]];
        ++i;
        stack[i] = stack[i-1];
      }
    }
    unsigned per[dim];
    std::fill(per, per + dim, 0);
    for (i = 0; i != dim; ++i) {
      ++per[i];
      g.insert_period(per);
      --per[i];
    }
    result.insert(g);
    return result;
  }
}


namespace ceta {
namespace impl {
  static rational gcd(const rational& x, const rational& y) {
    long long d = boost::gcd(x.denominator(), y.denominator());

    return rational(boost::gcd(x.numerator(), y.numerator()),
                    (x.denominator() / d) * y.denominator());
  }

  /**
   * Given a vector of rationals from fn to fnEnd, computes a vector
   * of integers maintaining the same ratio between elements.
   */
  static
  vector<int> scale_to_integers(const rational* start, const rational* end) {

    // Compute greatest common divisor of rational numbers
    rational result_gcd(0);

    for (const rational* i(start); i != end; ++i) {
      result_gcd = gcd(result_gcd, *i);
    }

    vector<int> result(std::distance(start, end));
    vector<int>::iterator iresult(result.begin());
    for (const rational* i(start); i != end; ++i) {
      *iresult = (*i / result_gcd).numerator();
      ++iresult;
    }
    return result;
  }

  /**
   * Chooses the best zero function from an lu factorization.
   */
  static
  void choose_min_fn(const LU<rational>& lu, int* weights) {
    unsigned bestSum(numeric_limits<unsigned>::max());
    bool bestPos(true);
    for (size_t iFn(0); lu.rank() + iFn != lu.nc(); ++iFn) {
      vector<int> cur_fn
        = scale_to_integers(lu.zero_fn(iFn), lu.zero_fn(iFn) + lu.nc());

      typedef vector<int>::const_iterator iter;

      unsigned posSum(0);
      unsigned negSum(0);
      for (iter i(cur_fn.begin()); i != cur_fn.end(); ++i) {
        if (*i < 0) {
          negSum -= *i;
        } else {
          posSum += *i;
        }
      }
      if ((negSum < posSum) && (negSum < bestSum)) {
        bestSum = negSum;
        std::copy(cur_fn.begin(), cur_fn.end(), weights);
        bestPos = false;
      } else if (posSum < bestSum) {
        bestSum = posSum;
        std::copy(cur_fn.begin(), cur_fn.end(), weights);
        bestPos = true;
      }
    }
    if (bestPos == false) {
      for (int* i(weights); i != weights + lu.nc(); ++i) {
        *i = -*i;
      }
    }
  }

  template<class T>
  class col_vector_matrix {
  public:
    col_vector_matrix(const vector<T*>& cols) : cols_(cols) {};
    const T& operator()(size_t r, size_t c) const { return cols_[c][r]; };
  private:
    const vector<T*>& cols_;
  };

  static
  void add_independent_periods(const linear_set_group& g,
      semilinear_set& result) {
    typedef set< vector<unsigned> > constant_set;

    typedef constant_set::iterator iter;
    typedef vector<unsigned*> period_key;

    // Mapping from periodKey identifying inactive periods to constant
    // vectors for that group of inactive periods.
    //
    // This mapping can be used as a queue in which sets with the most
    // active columns are on top.
    map<period_key, constant_set > queue;

    size_t dim = g.dim();
    size_t np = g.periods().size();

    // Initialize periods array
    int period_array[np * dim];
    copy_periods<true>(g, period_array);

    // Create initial key and start adding it to queue.
    period_key initial(np);
    {
      unsigned* iarray = reinterpret_cast<unsigned*>(period_array);

      typedef period_key::iterator iter;
      for (iter i(initial.begin()); i != initial.end(); ++i) {
        *i = iarray;
        iarray += dim;
      }
    }

    constant_set& initial_constants(queue[initial]);
    // Copy constants into set
    copy_arrays<vector<unsigned> >(g.dim(),
        g.constants().begin(), g.constants().end(),
        insert_iterator<constant_set>(initial_constants,
                                     initial_constants.begin()));

    // Pull top of queue off until empty
    while (queue.empty() == false) {
      const period_key& key(queue.begin()->first);
      constant_set& base_cons(queue.begin()->second);

      // LU decompose current periods
      LU<rational> lu(g.dim(), key.size(), col_vector_matrix<unsigned>(key));

      // If periods are linearly independent
      if (lu.rank() == lu.nc()) {
        linear_set_group new_group(g.dim());

        // Add base_cons to new_group
        for (iter i(base_cons.begin()); i != base_cons.end(); ++i) {
          new_group.insert_constant(&(*i)[0]);
        }

        // Add periods to new_group
        std::copy(key.begin(), key.end(),
                  period_insert_iterator<const unsigned*>(new_group));

        result.insert(new_group);
      } else {
        // Compute homogeneous solution equation
        int best_sol[key.size()];
        choose_min_fn(lu, best_sol);

        for (size_t ip(0); ip != key.size(); ++ip) {
          // For each positive value in homogenous solution
          if (best_sol[ip] > 0) {
            // Create key with current period removed
            period_key new_key(key.size() - 1);
            {
              period_key::const_iterator key_mid = key.begin() + ip;
              period_key::iterator new_mid = new_key.begin() + ip;

              std::copy(key.begin(), key_mid, new_key.begin());
              std::copy(key_mid + 1, key.end(), new_mid);
            }

            // Get period that is being removed.
            const unsigned* removed_period(key[ip]);

            // Get base_cons for new key (empty if none)
            constant_set& newCS(queue[new_key]);

            // Expand base_cons appropriately
            for (iter ic(base_cons.begin()); ic != base_cons.end(); ++ic) {
              unsigned c[g.dim()];
              // Copy original constant into c
              std::copy(ic->begin(), ic->end(), c);

              unsigned limit = best_sol[ip];
              for (unsigned i(0); i != limit; ++i) {
                // Add c to new base_cons
                newCS.insert(vector<unsigned>(c, c + g.dim()));

                axpy(1, removed_period, removed_period + g.dim(), c);
              }
            }
          }
        }
      }
      // Delete top of stack
      queue.erase(key);
    }
  }

  template<typename M, typename T = typename M::value_type >
  class minor_matrix {
  public:
    minor_matrix(M m, size_t row, size_t col)
      : m_(m), row_(row), col_(col) {};

    const T& operator()(size_t r, size_t c) const {
      // Increment location row/column accessed if either is
      // above removed row/column.
      if (r >= row_) ++r;
      if (c >= col_) ++c;
      return m_(r, c);
    }
  private:
    M m_;
    size_t row_;
    size_t col_;
  };

  template<class M>
  static
  int kmult(size_t n, M m) {
    LU<rational> lumain(n, n, m);

    long long num(std::abs(lumain.det().numerator()));
    long long div(num);

    for (size_t ir(0); ir != n; ++ir) {
      for (size_t ic(0); ic != n; ++ic) {
        long long r(std::abs(
          LU<rational>(n-1, n-1,
            minor_matrix<M>(m, ir, ic)).det().numerator()));
        div = boost::gcd(div, r);
      }
    }
    return num / div;
  }

  enum col_sign {zero_sign = 0, pos_sign = 1, neg_sign = -1};

  typedef std::vector<col_sign> sign_vector;

  static
  bool compatible_types(const sign_vector& x, const sign_vector& y) {
    bool compatible = (x.size() == y.size());

    typedef sign_vector::const_iterator iter;

    iter ix(x.begin());
    iter x_end(x.end());
    iter iy(y.begin());
    while (compatible && (ix != x_end)) {
      compatible = *ix * *iy >= 0;
      ++ix; ++iy;
    }
    return compatible;
  }

  static
  bool partially_le(const sign_vector& x, const sign_vector& y) {
    if (x.size() != y.size()) return false;
    // Indicates if x <= y in the partial order
    bool xple(true);
    for (size_t i(0); xple && (i != x.size()); ++i)
      xple = (x[i] == zero_sign) || (x[i] == y[i]);
    return xple;
  }

  static
  bool compatible_not_subsumed(const sign_vector& x, const sign_vector& y) {
    if (x.size() != y.size()) return false;
    // Indicates if x <= y in the partial order
    bool xple(true);
    // Indicates if y <= x in the partial order
    bool yple(true);
    for (size_t i(0); (i != x.size()); ++i) {
      xple = xple && ((x[i] == 0) || (x[i] == y[i]));
      yple = yple && ((y[i] == 0) || (x[i] == y[i]));
      if (x[i] * y[i] < 0) return false;
    }
    return (xple == false) && (yple == false);
  }

  static
  sign_vector make_sign_vector(size_t dim, const vector<unsigned>& v) {
    sign_vector result(dim);
    for (size_t i(0); i != dim; ++i) {
      if (v[dim+i] > 0) {
        result[i] = pos_sign;
      } else if (v[2*dim+i] > 0) {
        result[i] = neg_sign;
      } else {
        result[i] = zero_sign;
      }
    }
    return result;
  }

  static
  col_sign intersect_element(col_sign x, col_sign y) {
    return static_cast<col_sign>(x | y);
  }

  static
  sign_vector intersect_signs(const sign_vector& x, const sign_vector& y) {
    sign_vector result(std::min(x.size(), y.size()));
    std::transform(x.begin(), x.end(), y.begin(), result.begin(),
                   intersect_element);
    return result;
  }


  typedef map<sign_vector, set<vector<unsigned> > > sign_map_t;

  static
  set<sign_vector> most_specific_signs(const sign_map_t& types) {

    set<sign_vector> buffer;
    // Add all types into buffer
    typedef sign_map_t::const_iterator iter;
    for (iter i(types.begin()); i != types.end(); ++i) {
      buffer.insert(i->first);
    }

    // Build set containing all compatible combinations of types
    set<sign_vector> combos;
    while (buffer.empty() == false) {
      set<sign_vector>::iterator top(buffer.begin());

      for (set<sign_vector>::const_iterator cur(combos.begin());
           (cur != combos.end());
           ++cur) {
        if (compatible_not_subsumed(*top, *cur)
             && (combos.find(intersect_signs(*top, *cur)) == combos.end())) {
          buffer.insert(intersect_signs(*top, *cur));
        }
      }
      combos.insert(*top);
      buffer.erase(top);
    }

    // Delete non-maximal types from combos
    set<sign_vector>::iterator i(combos.begin());
    while (i != combos.end()) {
      set<sign_vector>::iterator j(i);
      ++j;


      bool erased = false;
      while (!erased && (j != combos.end())) {
        if (partially_le(*i, *j)) {
          // Delete i
          set<sign_vector>::iterator next(i);
          ++next;
          combos.erase(i);
          erased = true;
          i = next;
          j = combos.end();
        } else if (partially_le(*j, *i)) {
          // Delete j
          set<sign_vector>::iterator next(j);
          ++next;
          combos.erase(j);
          j = next;
        } else if (compatible_types(*i, *j)) {
          // Delete i and j
          combos.erase(j);
          set<sign_vector>::iterator next(i);
          ++next;
          combos.erase(i);
          erased = true;
          i = next;
          j = combos.end();
        } else {
          ++j;
        }
      }
      if (erased == false) ++i;
    }

    return combos;
  };

  static
  semilinear_set& operator+=(semilinear_set& x, const semilinear_set& y) {
    if (x.dim() > y.dim()) {
      throw std::logic_error("x.dim() cannot be smaller than y.dim()");
    }

    for (semilinear_set::iterator i(y.begin()); i != y.end(); ++i)
      x.insert(*i);
    return x;
  }

  /**
   * Return the complement of the linear set in N^dim with constant 0 and
   * periods [begin ... end).
   */
  template<class I>
  static
  semilinear_set zero_complement(size_t dim, I begin, I end)
  {
    // Construct a n * 3n matrix where (n = g.dim())
    // * the first n columns represent a n * n matrix equal to k * identity
    // * the second n columns represent the negation of each period
    // * the third n columns represent the periods
    int elements[3 * dim * dim];

    // We initialize elements in 4 steps:
    // First we initialize the g.np columns in the second group
    // Next we compute remaining n - g.np columns in group
    // Then we initialize the first group
    // Finally, we negate the periods to initialize the 3rd group

    // Initialize second n columns with first periods
    int* curPer(elements + dim * dim);
    size_t np(0);
    for (I i(begin); i != end; ++i) {
      std::copy(i->begin(), i->end(), curPer);
      curPer += dim;
      ++np;
    }
    col_matrix_view<int>
      pos_period_matrix(dim, dim, elements + dim * dim);

    // Complete periods with extra columns
    LU<rational> p(dim, np, pos_period_matrix);

    // Initialize new periods
    std::fill(elements + (dim + np) * dim,
              elements + 2 * dim * dim,
              0);
    for (size_t i(np); i != dim; ++i) {
      pos_period_matrix(p.row_idx()[i], i) = 1;
    }

    // Compute k(periods)
    long long k(kmult(dim, pos_period_matrix));

    // Initialize first n columns of elements to be k * identity matrix
    fill_identity_matrix(dim,
                         col_matrix_view<int>(dim, dim, elements),
                         k);

    // Initialize last n columns of elements
    transform(elements + dim * dim,
              elements + 2 * dim * dim,
              elements + 2 * dim * dim,
              negate<int>());

    // Compute homogeneous solutions to elements x = 0
    ld_solver_t solver(dim, 3 * dim, elements);

    // Mapping from each type to solutions with that type
    sign_map_t sign_map;
    vector<unsigned> next(3 * dim);
    while (solver.next(next)) {
      // Need to check that x should not be both positive and negative
      bool addSol = true;
      for (size_t i(0); addSol && (i != dim); ++i) {
        addSol = (next[dim + i] == 0) || (next[2 * dim + i] == 0);
      }
      if (addSol)
        sign_map[make_sign_vector(dim, next)].insert(next);
    }

    semilinear_set result(dim);

    set<sign_vector> max_signs = most_specific_signs(sign_map);

    typedef set<sign_vector>::iterator iter;

    // Compute W_{1\/2} for periods
    for (iter isign(max_signs.begin()); isign != max_signs.end(); ++isign) {
      linear_set_group new_group(dim);
      const sign_vector& type(*isign);

      // Indices stores which indices to check in solution. If a vector is
      // positive at one of these indices, then add it is a constant.
      size_t posidx[dim-1];
      size_t* posidxEnd(posidx);

      // Initialize posidx
      for (size_t i(0); i != np; ++i) {
        if (type[i] == pos_sign) {
          *posidxEnd = i;
          ++posidxEnd;
        }
      }
      for (size_t i(np); i != dim; ++i) {
        if (type[i] != zero_sign) {
          *posidxEnd = i;
          ++posidxEnd;
        }
      }

      if (posidx != posidxEnd) {
        typedef sign_map_t::iterator iter;
        for (iter im(sign_map.begin()); im != sign_map.end(); ++im) {
          if (partially_le(im->first, type)) {
            // Determine if vectors should be constants.
            bool isCons(false);
            for (size_t* pidx(posidx);
                 (isCons == false) && (pidx != posidxEnd);
                 ++pidx) {
              isCons = (im->first[*pidx] != 0);
            }
            set< vector<unsigned> >& solset(im->second);
            for (set< vector<unsigned> >::iterator iv(solset.begin());
                 iv != solset.end();
                 ++iv) {
              // insert_constant and period will just add first g.dim()
              // values to new_group
              if (isCons)
                new_group.insert_constant(&(*iv)[0]);
              new_group.insert_period(&(*iv)[0]);
            }
          }
        }
      }
      // Add group to result
      result.insert(new_group);
    }

    // Compute W_{3} for periods(g)

    // Form semilinear set with solution to K x = P y
    linear_set_group valid_group(dim + np);

    // Array of elements only holding zero
    unsigned zero_vector[dim + np];
    std::fill(zero_vector, zero_vector + dim + np, 0);

    valid_group.insert_constant(zero_vector);

    typedef map<sign_vector, set< vector<unsigned> > >::iterator sign_iter;
    for (sign_iter im = sign_map.begin(); im != sign_map.end(); ++im) {
      bool validsol(true);
      for (size_t i(0); validsol && (i != np); ++i) {
        validsol = (im->first[i] != pos_sign);
      }
      for (size_t i(np); validsol && (i != dim); ++i) {
        validsol = (im->first[i] == zero_sign);
      }
      if (validsol) {
        // Add each solution to set
        for (set< vector<unsigned> >::iterator iv = im->second.begin();
             iv != im->second.end();
             ++iv) {
          unsigned v[dim + np];
          std::copy(iv->begin(), iv->begin() + dim, v);
          std::copy(iv->begin() + 2*dim, iv->begin() + 2*dim + np, v + dim);
          valid_group.insert_period(v);
        }
      }
    }
    semilinear_set validsols(dim + np);
    validsols.insert(valid_group);

    semilinear_set uneven_multiples(dim + np);

    for (size_t ip(0); ip != np; ++ip) {
      // Create linear set group for uneven multiple of
      // k with period ip
      linear_set_group uneven(dim + np);


      // Add constant for each value in [1 ... k)
      for (size_t i(1); i != k; ++i) {
        ++zero_vector[dim + ip];
        uneven.insert_constant(zero_vector);
      }
      zero_vector[dim + ip] = 0;

      // Add periods
      for (size_t i(0); i != dim + np; ++i) {

        zero_vector[i] = (i == dim + ip) ? k : 1;
        uneven.insert_period(zero_vector);
        zero_vector[i] = 0;
      }
      uneven_multiples.insert(uneven);
    }

    result += intersect(validsols, uneven_multiples);

    return result;
  }

  // Given an offset and a linear set group returns the semilinear set
  // containing every element with a component less than the offset and every
  // other element such that (x - offset) is in g.
  // size_t
  static
  semilinear_set increment_inclusive(const std::vector<unsigned>& offset,
                                     const semilinear_set& set) {
    size_t dim = set.dim();
    semilinear_set result(set.dim());

    // Add space below offset to result.
    for (size_t i(0); i != set.dim(); ++i) {
      linear_set_group belowgroup(set.dim());

      unsigned zero_vector[dim];
      std::fill(zero_vector, zero_vector + dim, 0);

      for (unsigned val(0); val != offset[i]; ++val) {
        // Add constant
        belowgroup.insert_constant(zero_vector);
        ++zero_vector[i];
      }
      zero_vector[i] = 0;

      // For every j != i, add period e_j
      for (unsigned j(0); j != set.dim(); ++j) {
        if (j != i) {
          zero_vector[j] = 1;
          belowgroup.insert_period(zero_vector);
          zero_vector[j] = 0;
        }
      }
      result.insert(belowgroup);
    }

    typedef semilinear_set::iterator sls_iter;

    // Copy set with constants incremented by *ic into result
    for (sls_iter iset(set.begin()); iset != set.end(); ++iset) {
      const linear_set_group& group(*iset);
      linear_set_group copy(set.dim());

      typedef linear_set_group::iterator lsg_iter;

      lsg_iter c_begin = group.constants().begin();
      lsg_iter c_end   = group.constants().end();
      for (lsg_iter ic(c_begin); ic != c_end; ++ic) {
        unsigned v[set.dim()];
        for (size_t i(0); i != set.dim(); ++i)
          v[i] = offset[i] + (*ic)[i];
        copy.insert_constant(v);
      }

      // Copy periods from orig into copy
      lsg_iter p_begin = group.periods().begin();
      lsg_iter p_end   = group.periods().end();
      for (lsg_iter i(p_begin); i != p_end; ++i)
        copy.insert_period(&i->begin()[0]);
      result.insert(copy);
    }
    return result;
  }
}}

namespace ceta {
  semilinear_set independent_periods(const semilinear_set& set) {
    typedef semilinear_set::iterator iter;

    semilinear_set result(set.dim());
    for (iter i = set.begin(); i != set.end(); ++i)
      add_independent_periods(*i, result);
    return result;
  }

  /**
   * Return the complement of the lsg_impl g
   */
  static
  semilinear_set complement(const linear_set_group& g) {
    semilinear_set zc
        = zero_complement(g.dim(), g.periods().begin(), g.periods().end());

    semilinear_set result(complete_set(g.dim()));

    typedef linear_set_group::iterator iter;
    iter c_begin = g.constants().begin();
    iter c_end = g.constants().end();

    for (iter ic(c_begin); !is_empty(result) && (ic != c_end); ++ic)
      result = intersect(result, increment_inclusive(*ic, zc));
    return result;
  }
  semilinear_set complement(const semilinear_set& set) {
    // First construct semilinear set with linearly independent periods
    semilinear_set si(independent_periods(set));

    // Complement each linear set group
    if (si.begin() == si.end())
      return complete_set(set.dim());

    semilinear_set::iterator i(si.begin());
    semilinear_set result(complement(*i));
    ++i;

    while (!is_empty(result) && (i != si.end())) {
      result = intersect(result, complement(*i));
      ++i;
    }
    return result;
  }

  bool is_empty(const semilinear_set& set) {
    return set.begin() == set.end();
  }
}
