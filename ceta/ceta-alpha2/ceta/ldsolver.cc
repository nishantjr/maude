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
#include "ldsolver.hh"
#include "matrix.hh"

#include <map>
#include <boost/rational.hpp>

//#define MAUDE_SOLVER
//#define MAUDE_USE_GCD
//#define GAUSSIAN_EXTENSIONS
//#define PROFILE_NODES


#ifdef MAUDE_SOLVER
#include <macros.hh>
#include <vector.hh>
#include <mpzSystem.hh>
#endif

using namespace ceta;
using namespace std;

typedef boost::rational<long long> rational;

/**
 * Returns true if v is a vector of only zeros
 */
template <typename I>
static
bool is_zero(I start, I end) {
  for (I i(start); i != end; ++i) {
    if (*i != 0)
      return false;
  }
  return true;
}

namespace ceta {
namespace impl {
  /**
   * Predicate for lexiographically comparing arrays of a fixed length
   */
  class strict_lexicographical_ordering {
  public:
    strict_lexicographical_ordering(size_t n) : n_(n) {}
  
    template<class I>
    bool operator()(I x, I y) {
      return std::lexicographical_compare(x, x + n_, y, y + n_);
    }
  private:
    size_t n_;
  };

  class node_stack {
    // The node stack for solving a LD system with p equations and q
    // variables is a stack with a maximum of q nodes.
    //
    // Each node has
    // 1. Current Remainer (p integers)
    // 2. Current solution (q solution_elts)
    // 3. Bit vector of frozen positions (q booleans)
    // Want node to occupy contiguous section of memory
    // Need to override new and delete array operators.
    // Need to remove all implicit constructors and assignment operators.
  public:
    node_stack(size_t eqn_count, size_t var_count)
      : nr_(eqn_count),
        nc_(var_count),
        solution_offset_(sizeof(int) * eqn_count),
        frozen_offset_(solution_offset_ + sizeof(unsigned) * var_count),
        rank_offset_(frozen_offset_ +
                    // Compute size of frozen vars to align records on
                    // integer boundaries.  Note that sizeof(bool) is not
                    // necessarily 1, and on some architectures may be larger
                    // than sizeof(int)!
                    (sizeof(bool) < sizeof(int) ?
                      sizeof(int)
                          * (sizeof(bool) * var_count / sizeof(int) + 1) :
                      sizeof(bool) * var_count)),
        node_size_(rank_offset_ + sizeof(size_t)),
        stack_(new char[node_size_ * (var_count + 1)]),
        next_node_(stack_) {

      solution_offset_ -= node_size_;
      frozen_offset_ -= node_size_;
      rank_offset_ -= node_size_;
      std::fill(stack_, stack_ + node_size_ * var_count, 0);
    }

    ~node_stack() {
      delete [] stack_;
    }
  
    size_t count(void) {
      return (next_node_ - stack_) / node_size_;
    }

    bool is_empty(void) {
      return stack_ == next_node_;
    }
  
    int* remainder(void) {
      return reinterpret_cast<int*>(next_node_ - node_size_);
    }

    unsigned* solution(void) {
      return reinterpret_cast<unsigned*>(next_node_ + solution_offset_);
    }

    bool* frozen_vars(void) {
      return reinterpret_cast<bool*>(next_node_ + frozen_offset_);
    }

    size_t& rank(void) {
      return *(reinterpret_cast<size_t*>(next_node_ + rank_offset_));
    }
    
    void clear(void) {
      next_node_ = stack_;
    }
    
    void push(void) {
      std::fill(next_node_, next_node_ + node_size_, 0);
      next_node_ += node_size_;
    }
  
    void pop(void) {
      next_node_ -= node_size_;
    }

    // Given a coefffient matrix explore the list of variable indices ranging
    // from varStart ... varEnd - 1, expl
    void explore_nodes(const col_matrix<int>& m, 
                       const size_t* varStart, const size_t* varEnd) {
      // Decrement stack to reflect that current stack is being deleted.
      next_node_ -= node_size_;
    
      // Get location of last var to expand if any.
      const size_t* lastVar = (varEnd == varStart) ? NULL : (varEnd - 1);
      
      for (const size_t* curVar(varStart); curVar != varEnd; ++curVar) {
        // Get index of variable to increment
        size_t var(*curVar);
    
        // Store index of next index in stack to use
        char* next = next_node_ + node_size_;
    
        // Before we change anything with the next node, we want to 
        // copy the current node state into the node after the next
        // one and freeze the current var in that state.
        if (curVar != lastVar) {
          // Copy current stack to next stack position
          std::copy(next_node_, next_node_ + node_size_, next);
          // Freeze current var in next node.
          bool* frozenVars
              = reinterpret_cast<bool*>(next + node_size_ + frozen_offset_);
          frozenVars[var] = true;
        }
    
        // Move nextNode is stack to next
        next_node_ = next;
        // Increment solution at var
        ++(solution()[var]);
        // Adjust remainder to reflect incremented solution
        axpy(1, m.col(var).begin(), m.col(var).end(), remainder());
      }
    }
    
  private:
    // Disable copy constructor and assignment
    node_stack(const node_stack&);
    node_stack& operator=(const node_stack&);
    
    const size_t nr_;
    const size_t nc_;
    ptrdiff_t solution_offset_;
    ptrdiff_t frozen_offset_;
    ptrdiff_t rank_offset_;
    const size_t node_size_;
    char* const stack_;
    char* next_node_;
  };

  /**
   * Returns true if every element from range [start1 ... end1) is less than
   * or equal to the corresponding element in range
   * [start2 ... start2 + (end1 - start1)).
   */
  template <typename I1, typename I2>
  static
  bool elementwise_less(I1 start1, I1 end1, I2 start2) {
    I1 ele1(start1);
    I2 ele2(start2);
    bool result = true;
    while (result && (ele1 != end1)) {
      result = (*ele1 <= *ele2);
      ++ele1;
      ++ele2;
    }
    return result;
  }

  class solution_list {
  public:
    solution_list(size_t nc)
      : nc_(nc),
        s_() {
    }

    ~solution_list() {
      clear();
    }
  
    void add(const unsigned* sol) {
      unsigned* newsol = new unsigned[nc_];
      try {
        std::copy(sol, sol + nc_, newsol);
        s_.push_back(newsol);
      } catch (...) {
        delete [] newsol;
        throw;
      }
    }

    void clear(void) {
      typedef vector<const unsigned*>::const_iterator iter;

      for (iter i = s_.begin(); i != s_.end(); ++i) {
        delete [] *i;
      }
      s_.clear();
    }

    /** Returns true if no previous solution is elementwise less than sol. */
    bool is_min(const unsigned* sol) const {
      typedef vector<const unsigned*>::const_iterator iter;

      bool result = true;
      for (iter i = s_.begin(); result && (i != s_.end()); ++i)
        result = !elementwise_less(*i, *i + nc_, sol);
      return result;
    }

    size_t count() const {
      return s_.size();
    }
  private:
    // Disable copy constructor and assignment operator
    solution_list(const solution_list&);
    solution_list& operator=(const solution_list&);
  
    const size_t nc_;
    vector<const unsigned*> s_;
  };

  class lu_factory {
    typedef std::map<const bool*, LU<rational>*,
                     strict_lexicographical_ordering> map_type;
  
  public:
    lu_factory(size_t nr, size_t nc)
      : nr_(nr), nc_(nc), map_(strict_lexicographical_ordering(nc)) {
    }
  
    ~lu_factory() {
      map_type::iterator i = map_.begin();
      while (i != map_.end()) {
        map_type::iterator next = i;
        ++next;
        const bool* frozen_cols = i->first;
        LU<rational>* lu = i->second;
        map_.erase(i);
        delete [] frozen_cols;
        delete lu;
        i = next;
      }
    }
  
    size_t size(void) const {
      return map_.size();
    }
    
    const LU<rational>* get(const bool* frozen_cols,
                            size_t unfrozen_count,
                            const size_t* unfrozen_indices,
                            const col_matrix<int>& m) {
      map_type::const_iterator i = map_.find(frozen_cols);
      LU<rational>* lu = NULL;
      if (i != map_.end()) {
        lu = i->second;
      } else {
        bool* frozen_copy = NULL;
        try {
          // Initialize copy of frozen_cols
          frozen_copy = new bool[nc_];
          std::copy(frozen_cols, frozen_cols + nc_, frozen_copy);
  
          // Create lu matrix for frozen_cols
          lu = new LU<rational>(nr_, unfrozen_count, 
                make_col_permutation_matrix_view(m, unfrozen_indices));
  
           map_.insert(make_pair(frozen_copy, lu));
        } catch (...) {
          delete [] frozen_copy;
          delete lu;
          throw;
        }
      }
      return lu;
    }
  private:
    // Disable default copy constructor and assignment operator
    lu_factory(const lu_factory&);
    lu_factory& operator=(const lu_factory&);
    
    size_t nr_;
    size_t nc_;
    map_type map_;
  };

  /**
   * Given a range [start end), this returns the distance from start of
   * each element that equals value.  Returns the position in indices
   * at end of list
   */
  template<typename I, typename T>
  static
  size_t* indices_with_value(I start, I end, T value, size_t* indices) { 
    size_t idx = 0;
    for (I i = start; i != end; ++i, ++idx) {
      if (*i == value) {
        *indices = idx;
        ++indices;
      }
    }
    return indices;
  }
}}

using namespace ceta::impl;

namespace ceta {
#ifdef MAUDE_SOLVER
  class ld_solver_impl {
  public:
    ld_solver_impl(size_t nr, size_t nc, const int* coefficients)
      : nr_(nr),
        nc_(nc),
        coefs_(coefficients, coefficients + nr * nc),
        system_(new MpzSystem()),
        homo_(true) {
      // Copy coefficients into system to begin solving homogeneous case.
      MpzSystem::IntVec eqn(nc);
      for (size_t row = 0; row != nr; ++row) {
        for (size_t col = 0; col != nc; ++col)
          eqn[col] = coefs_[col * nr_ + row];
        system_->insertEqn(eqn);
      }
      // Set bounds
      for (size_t col = 0; col != nc; ++col)
        eqn[col] = UNBOUNDED;
      system_->setUpperBounds(eqn);
    }

    size_t nr(void) const {
      return nr_;
    }

    size_t nc(void) const {
      return nc_;
    }

    void solve(const int* v) {
      system_.reset(new MpzSystem());
      homo_ = false;
      // Copy coefficients offset by one.
      MpzSystem::IntVec eqn(nc_ + 1);
      for (size_t row = 0; row != nr_; ++row) {
        eqn[0] = -v[row];
        for (size_t col = 0; col != nc_; ++col)
          eqn[col + 1] = coefs_[col * nr_ + row];
        system_->insertEqn(eqn);
      }
      // Set bounds
      eqn[0] = 1;
      for (size_t col = 0; col != nc_; ++col)
        eqn[col + 1] = UNBOUNDED;
      system_->setUpperBounds(eqn);
    }

    bool next(vector<unsigned>& sol) {
      if (homo_) {
        MpzSystem::IntVec msol(nc_);
        #ifdef MAUDE_USE_GCD
        if (system_->findNextMinimalSolutionGcd(msol)) {
        #else
        if (system_->findNextMinimalSolution(msol)) {
        #endif
          for (size_t i = 0; i != nc_; ++i)
            sol[i] = msol[i].get_ui();
          return true;
        }
      } else {
        MpzSystem::IntVec msol(nc_ + 1);
        #ifdef MAUDE_USE_GCD
        while (system_->findNextMinimalSolutionGcd(msol)) {
        #else
        while (system_->findNextMinimalSolution(msol)) {
        #endif
          if (msol[0] == 1) {
            for (size_t i = 0; i != nc_; ++i)
              sol[i] = msol[i + 1].get_ui();
            return true;
          }
        }
      }
      return false;
    }
  private:
    const size_t nr_;
    const size_t nc_;
    const vector<int> coefs_;
    auto_ptr<MpzSystem> system_;
    bool homo_;
  };
#else
  class ld_solver_impl {
  public:
    ld_solver_impl(size_t nr, size_t nc, const int* coefficients)
      : nr_(nr),
        nc_(nc),
        m_(nr, nc, coefficients),
        stack_(nr, nc),
        homo_complete_(false),
        hSol_(nc),
        inhSol_(nc)
    #ifdef GAUSSIAN_EXTENSIONS
        ,cache_(nr, nc)
        ,independentNodes(0)
    #endif
    #ifdef PROFILE_NODES
        ,nodesExplored(new size_t[nc])
    #endif
    {
      stack_.push();
      stack_.rank() = nc_;
      size_t columns[nc_];
      for (size_t i = 0; i != nc_; i++)
        columns[i] = i;
      stack_.explore_nodes(m_, columns, columns + nc);
    #ifdef PROFILE_NODES
      std::fill(nodesExplored, nodesExplored + nc_, 0);
    #endif
    }

    size_t nr(void) const {
      return nr_;
    }

    size_t nc(void) const {
      return nc_;
    }

    void solve(const int* v) {
      vector<unsigned> sol(nc_);
      // Solve all homogeneous solutions if we haven't already
      while (!homo_complete_)
        next(sol);
      
      // Reset stack and inhomogeneous solutions to clean slate
      stack_.clear();
      inhSol_.clear();
      
      // Add single element in stack with remainder offset by -v[i].
      stack_.push();
      int* r = stack_.remainder();
      for (size_t i = 0; i != nr_; ++i)
        *(r++) = -*(v++);
      stack_.rank() = nc_;
    }

    bool next(std::vector<unsigned>& sol) {
      bool result = false;
    
      while (!result && (!stack_.is_empty())) { 
    
        // Get locations from top of stack
        int* remainder = stack_.remainder();
        unsigned* solution = stack_.solution();
        bool* frozen_vars = stack_.frozen_vars();
    
        // Number of variables that are not frozen
        size_t unfrozen_count = nc_ - (stack_.count() - 1);
        
        #ifdef PROFILE_NODES
        ++(nodesExplored[stack_.count() - 1]);
        #endif
        #ifdef GAUSSIAN_EXTENSIONS
        size_t& rank = stack_.rank();
        size_t unfrozen_indices[unfrozen_count];
        const LU<rational>* lu = NULL;
        if (unfrozen_count <= rank) {
          // Initialize unfrozen_indices
          indices_with_value(frozen_vars, frozen_vars + nc_, false, 
                             unfrozen_indices);
          lu = cache_.get(frozen_vars, unfrozen_count, unfrozen_indices, m_);
          rank = lu->rank();
        }
        
        // If the number of active variables equals the rank of the matrix
        // then try solving directly.
        if (unfrozen_count == rank) {
          independentNodes++;
    
          rational rem_solution[unfrozen_count];
          bool found = lu->solve(remainder, rem_solution);
    
          for (size_t i(0); found && (i != unfrozen_count); ++i) {
            if (rem_solution[i].numerator()  > 0) found = false;
            if (rem_solution[i].denominator() != 1) found = false;
          }
          stack_.pop();
          if (found) {
    	    for (size_t i(0); i != rank; ++i)
    	      solution[unfrozen_indices[i]] -= rem_solution[i].numerator();
    
            bool is_min = hSol_.is_min(solution)
                     && inhSol_.is_min(solution);
    	    if (is_min) {
              result = true;
              if (homo_complete_) {
                inhSol_.add(solution);
              } else {
                hSol_.add(solution);
              }
              std::copy(solution, solution + nc_, sol.begin());
            }
          }
        } else 
        #endif
        // If top of stack is solution
        if (is_zero(remainder, remainder + nr_)) {
          // Add top solution to proper list of solutions
          stack_.pop();
          result = true;
          if (homo_complete_) {
            inhSol_.add(solution);
          } else {
            hSol_.add(solution);
          }
          std::copy(solution, solution + nc_, sol.begin());
        } else { // if top of stack is not a solution
          // Search for which variables to increment further
          //
          // next_cols should contain the indices of which column to
          // increment further.
          size_t next_cols[unfrozen_count];
          // fEnd identifies the end of next_cols list
          size_t* fEnd = next_cols;
          // For each column in matrix
          for (size_t i = 0; i != nc_; i++) {
            // Figure out which columns should be new solutions.
            // If i is not frozen
            //    and dot product of column and remainder is negative
            if ((*frozen_vars == false)
               && (dot_product(m_.col(i).begin(), m_.col(i).end(),
                               remainder) < 0)) {
              // Temporarily increment solution at index i.
              ++solution[i]; 
              // Check if solution would still be minimal
              bool explore = hSol_.is_min(solution)
                        && inhSol_.is_min(solution);
              // Decrement solution at index i
              --solution[i];
              if (explore) {
    	        *fEnd = i;
    	        ++fEnd;
    	      }
            }
            frozen_vars++;
          }
          stack_.explore_nodes(m_, next_cols, fEnd);
        } // if top of stack not a solution
      }
    #ifdef PROFILE_NODES
      size_t total = 0;
      for (size_t i = 0; i < nc_; ++i) {
        total += nodesExplored[i];
        cout << "nodesExplored[" << i << "]: " << nodesExplored[i] << endl;
      }
      cout << "total: " << total << endl;
    #ifdef GAUSSIAN_EXTENSIONS
      cout << "independent nodes: " << independentNodes << endl;
      cout << "total decompositions: " << cache_.size() << endl;
    #endif
    #endif
      // If we cleared the stack and never found a solution
      if (result == false) {
        // We are definately done with homogeneous equations.
        homo_complete_ = true;
      }
      return result;
    }
  private:
    // Disable copy constructor and assignment operator
    ld_solver_impl(const ld_solver_impl& );
    ld_solver_impl& operator=(const ld_solver_impl&);

    const size_t nr_;
    const size_t nc_;
    const col_matrix<int> m_;
    node_stack stack_;
    bool homo_complete_;
    /** List of solutions found already for homogeneous equation Ax = 0 */
    solution_list hSol_;
    /** List of solutions found already for inhomogeneous equation Ax = v */
    solution_list inhSol_;
#ifdef GAUSSIAN_EXTENSIONS
    lu_factory cache_;
    size_t independentNodes;
#endif
#ifdef PROFILE_NODES
    size_t* nodesExplored;
#endif
  };
#endif

  ld_solver_t::ld_solver_t(size_t nr, size_t nc, const int* coef)
    : solver_(new ld_solver_impl(nr, nc, coef)) {
  }
  
  ld_solver_t::~ld_solver_t() {
    delete solver_;
  }
  
  void ld_solver_t::solve(const int* v) {
    solver_->solve(v);
  }
  
  const bool ld_solver_t::next(vector<unsigned>& sol) {
    return solver_->next(sol);
  }
  
  size_t ld_solver_t::nr(void) const {
    return solver_->nr();
  }
  
  size_t ld_solver_t::nc(void) const {
    return solver_->nc();
  }

}

