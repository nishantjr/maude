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
#include <algorithm>
#include <functional>
#include <list>
#include <map>
#include <vector>

#include <boost/utility.hpp>

#include "combinations.hh"
#include "parikh.hh"
#include "sls.hh"
#include "writer.hh"

#include <iostream>

using namespace ceta::cfg;
using namespace std;

namespace ceta {
namespace cfg {

  class symbol_impl {
  public:
    symbol_impl(symbol_type_t type, const char* id, size_t index)
      : type_(type),
        id_(id),
        index_(index) {
    }

    symbol_type_t type(void) const {
      return type_;
    }

    string id(void) const {
      return id_;
    }

    size_t index(void) const {
      return index_;
    }
  private:
    symbol_type_t type_;
    string id_;
    size_t index_;
  };

  symbol_type_t symbol_t::type(void) const {
    return impl_->type();
  }
  
  string symbol_t::id(void) const {
    return impl_->id();
  }

  size_t symbol_t::index(void) const {
    return impl_->index();
  }
}
}

namespace ceta {
namespace impl {
  /**
   * Enumerated type for representing a counting system with three numbers:
   * zero, one, and many.
   */
  enum three_counter { zero, one, many };
  
  static
  three_counter operator+(const three_counter& x, const three_counter& y) {
    switch (x) {
    case zero:
      return y;
      break;
    case one:
      if (y == zero) {
        return one;
      } else {
        return many;
      }
      break;
    default:
      return many;
    }
  }
  
  static
  three_counter& operator+=(three_counter& x, const three_counter& y) {
    return x = x + y;
  }

  typedef map<symbol_t, size_t> leaf_counts_t; 

  class base_tree {
  public:
    /** Create an empty initialized base_tree. */
    base_tree(void) 
      : nonterminal_leaf_count_(),
        in_tree_(),
        leaf_counts_() {
    }
  
    void set_root(symbol_t root) {
      root_ = root;
      in_tree_.insert(root);
    }
  
    const symbol_t& root(void) const {
      return root_;
    }

    three_counter& nonterminal_leaf_count(void) {
      return nonterminal_leaf_count_;
    }
  
    const three_counter& nonterminal_leaf_count(void) const {
      return nonterminal_leaf_count_;
    }
  
    symbol_t& nonterminal_leaf(void) {
      return nonterminal_leaf_;
    }
  
    const symbol_t& nonterminal_leaf(void) const {
      return nonterminal_leaf_;
    }
  
    const set<symbol_t>& nonterminal_set(void) const {
      return in_tree_;
    }

    bool in_tree(symbol_t symbol) const {
      return in_tree_.count(symbol) > 0;
    }
  
    void insert_in_tree(symbol_t symbol) {
      in_tree_.insert(symbol);
    }
  
    const leaf_counts_t& leaf_map(void) const {
      return leaf_counts_;
    }

    const size_t leaf_counts(symbol_t symbol) const {
      leaf_counts_t::const_iterator i = leaf_counts_.find(symbol);
      
      return (i != leaf_counts_.end()) ? i->second : 0;
    }
  
    /**
     * Returns true if this base tree is subsumed by o.  This is true when
     * this base tree has same root, non_terminal_leaf, and leaf_counts as 
     * o and every non_terminal in this tree is in o.
     */
    bool subsumed_by(const base_tree& o) const {
      bool result((root_ == o.root_)
          && (nonterminal_leaf_ == o.nonterminal_leaf_)
          && (leaf_counts_ == o.leaf_counts_));
      
      // Determine if o has more states than this
      typedef set<symbol_t>::const_iterator iter;
      
      for (iter i = in_tree_.begin(); result && (i != in_tree_.end()); ++i) {
        result = o.in_tree(*i);
      }
      return result;
    }

    /**
     * Adds leafs and nonterminals of y into this.  The root is not changed.
     */
    base_tree& operator+=(const base_tree& o) {
      // Update nonterminal_leaf
      nonterminal_leaf_count_ += o.nonterminal_leaf_count_;
      
      if (o.nonterminal_leaf_count_ == one) 
        nonterminal_leaf_ = o.nonterminal_leaf_;
    
      // Union in_tree_ with o.in_tree_
      in_tree_.insert(o.in_tree_.begin(), o.in_tree_.end());

      // Add vectors together
      typedef leaf_counts_t::const_iterator iter;
      for (iter i = o.leaf_counts_.begin(); i != o.leaf_counts_.end(); ++i) {
        leaf_counts_t::iterator iv = leaf_counts_.find(i->first);

        if (iv == leaf_counts_.end()) {
          leaf_counts_.insert(make_pair(i->first, i->second));
        } else {
          iv->second += i->second;
        }
      }
      return *this;
    }

  protected:
    /** Root symbol of tree - this must be a non-terminal. */
    symbol_t root_;
  
  
    /** Stores very generally how many non-terminals are leafs in tree. */
    three_counter nonterminal_leaf_count_;
  
    /** 
     * non_terminal_leaf_ stores index of non-terminal symbol appearing as a
     * leaf.  Only valid if nonterminal_leaf_count = one.
     */
    symbol_t nonterminal_leaf_;
  
    /** 
     * in_tree_ stores which nonterminals appear in a nonleaf positions in
     * the tree.  The size equals the number of nonterminals.
     */
    set<symbol_t> in_tree_;
  
    /**
     * leaf_counts_ stores number of occurances of each terminal symbol in
     * leaves.  Its size equals the number of terminals.
     */
    leaf_counts_t leaf_counts_;
  };

  /**
   * base_tree_list maintains a list of all trees that have been generated
   * in initial part of parikh contruction where trees that contain at most
   * one non-terminal in a leaf are constructed and the tree contains no
   * repetitions along path except that the non-terminal at the leaf may 
   * be also be the root non-terminal.
   */
  class base_tree_list : boost::noncopyable {
  public:
    typedef const base_tree& const_reference;
    typedef list<base_tree>::const_iterator iterator;
  
    /**
     * Constructs a base_tree list for specified number of terminals
     * and nonterminals.
     */
    base_tree_list(const list<symbol_impl>& nonterminals)
      : active_trees_(),
        periods_() {

      typedef list<symbol_impl>::const_iterator iter;
      for (iter i = nonterminals.begin(); i != nonterminals.end(); ++i) {
        list<base_tree> list;
        list.push_back(base_tree());
  
        // Initialize end of list to be singleton nonterminal
        base_tree& tree(list.back());
        tree.set_root(&*i);
        tree.nonterminal_leaf_count() = one;
        tree.nonterminal_leaf() = &*i;
        
        list.push_back(base_tree());
        active_trees_.insert(make_pair(&*i, list));
      }
    }
    
    /**
     * Attempts to insert a new tree with index root and whose immeadiate
     * subtrees are args into tree.  If the root already appears in the.
     */
    void push_back(const base_tree& tree) {
      active_trees_[tree.root()].back() = tree;
      active_trees_[tree.root()].push_back(base_tree());
    }
  
    void insert_period(const base_tree& tree) {
      periods_.push_back(tree);
    }
  
    iterator begin(symbol_t symbol) const {
      return active_trees_.find(symbol)->second.begin();
    }
  
    iterator end(symbol_t symbol) const {
      iterator result = active_trees_.find(symbol)->second.end();
      --result;
      return result;
    }
  
    const list<base_tree>& periods() const {
      return periods_;
    }
  private:
    /** 
     * This stores all trees we have contructed so far that does not have a
     * non-terminal appearing more than once along a path.  This is
     * organized as a map where each tree is in the list whose key is the
     * root symbol of the list.
     */
    map<symbol_t, list<base_tree> > active_trees_;
    
    /**
     * A list storing all the periods which have been constructed.  A period
     * contains its nonterminal root as its only nonterminal leaf and at
     * least one other leaf.
     */
    list<base_tree> periods_;
  };

  /** tran_t extends base trees to allow arguments to be added into it. */
  class tran_t : public base_tree {
  public:
    tran_t(const symbol_t* lhs_begin, const symbol_t* lhs_end, symbol_t rhs)
      : base_tree(),
        args_() {
  
      set_root(rhs);
      for (const symbol_t* i = lhs_begin; i != lhs_end; ++i) {
        // If this is a terminal
        if ((*i)->type() == terminal) {
          // Increment leaf counts
          leaf_counts_t::iterator ileaf = leaf_counts_.find(*i);
          if (ileaf == leaf_counts_.end()) {
            leaf_counts_.insert(make_pair(*i, 1));
          } else {
            ++ileaf->second;
          }
        } else {
          in_tree_.insert(*i);
          args_.push_back(*i);
        }
      }
    }
  
    const vector<symbol_t>& args() const {
      return args_;
    }
  
    void explore(const base_tree_list::iterator* inputs,
                 base_tree_list& values,
                 bool& new_input,
                 bool& abort) const {
      typedef const base_tree_list::iterator iterator;
  
      // Number of nonterminal leafs found.
      three_counter nonterminal_leaf_count(zero);
      // last nonterminal found 
      symbol_t nonterminal_leaf;
      // If exploration should be aborted because of incompatibilities
      bool is_period = false;
      bool invalid_args = false;
  
      iterator* inputs_end(inputs + args_.size());
      for (iterator* i(inputs); !invalid_args && (i != inputs_end); ++i) {
        const base_tree& tree(**i);
        nonterminal_leaf_count += tree.nonterminal_leaf_count();
        if (tree.nonterminal_leaf_count() == one)
          nonterminal_leaf = tree.nonterminal_leaf();
  
        is_period = (nonterminal_leaf_count == one)
                 && (nonterminal_leaf == root_);
  
        // Check if should be invalid
        invalid_args = (nonterminal_leaf_count == many) 
            || (tree.in_tree(root_) && !is_period);
      }
  
      // Abort if there are many nonterminal leafs
      if (invalid_args == false) {
        base_tree result(*this);
        result.nonterminal_leaf_count() = nonterminal_leaf_count;
        result.nonterminal_leaf() = nonterminal_leaf;
        for (iterator* i(inputs); i != inputs_end; ++i)
          result += **i;
  
        // If we have a non-terminal leaf equal to new root
        if (is_period) {
          values.insert_period(result);
        } else {
          values.push_back(result);
          new_input = true;
        }
      }
    }
  private:
    // Disable assignment operator
    tran_t& operator=(const tran_t&);
  
    vector<symbol_t> args_;
  };

  class constant_list : boost::noncopyable {
  public:
    typedef list<base_tree>::const_iterator iterator;
  
    constant_list(void) {
      list_.push_back(base_tree());
    }
  
    iterator begin(void) const {
      return list_.begin();
    }
  
    iterator end(void) const {
      return --list_.end();
    }
    
    /**
     * Inserts a copy of tree into the list.  Return true if list is added.
     */
    bool insert(const base_tree& tree) {
      typedef list<base_tree>::iterator iterator;
      bool subsumed(false);
      // Check to see if constant is subsumed
      for (iterator i(list_.begin()); !subsumed && (i != list_.end()); ++i) {
        subsumed = tree.subsumed_by(*i);
      }
      if (!subsumed) {
        list_.back() = tree;
        list_.push_back(base_tree());
      }
      return !subsumed;
    }
  private:
    // List of all constants added to list.
    list<base_tree> list_;
  };
  
  class period : public base_tree {
  public:
    period(const base_tree& tree)
      : base_tree(tree) {
    }
  
    void explore(const base_tree& constant,
                 constant_list& constants) const {
      
      // If the root symbol already appears in the constant.
      if (constant.in_tree(root_)) {
        typedef set<symbol_t>::const_iterator iter;

        // See if this period would add a new non-terminal to constant.
        bool new_nt = false;
        
        iter p_end = in_tree_.end();
        for (iter i = in_tree_.begin(); !new_nt && (i != p_end); ++i)
          new_nt = !constant.in_tree(*i);

        // Add period to constant if it adds a new non-terminal.
        if (new_nt) {
          base_tree clone(constant);
          constants.insert(clone += *this);
        }
      }
    }
  };

  void initialize_vector(const base_tree& t, unsigned* v) {
    typedef leaf_counts_t::const_iterator iter;

    const leaf_counts_t& lc = t.leaf_map();
    for (iter i = lc.begin(); i != lc.end(); ++i) {
      v[i->first->index()] = i->second;
    }
  }

  typedef list<tran_t>::const_iterator tran_iter;

  void base_combinations(const tran_iter fn_begin, const tran_iter fn_end,
                         base_tree_list& values) {
    typedef vector<symbol_t>::const_iterator arg_iter;
    typedef base_tree_list::iterator list_iter;
  
    // Stores total number of inputs for all functions
    size_t total_arg_count(0);
  
    // Initialize total_arg_count
    for (tran_iter ifn = fn_begin; ifn != fn_end; ++ifn) 
      total_arg_count += ifn->args().size();
   
    // Stores index of input we have already processed
    list_iter prev_inputs[total_arg_count];
    // Initialize prev_inputs
    {
      list_iter* cur_last(prev_inputs);
      for (tran_iter ifn = fn_begin; ifn != fn_end; ++ifn) {
        for (arg_iter i = ifn->args().begin(); i != ifn->args().end(); ++i) {
          *cur_last = values.begin(*i);
          ++cur_last;
        }
      }
    }
    
    // Indicates if current function has found a new input
    bool new_input = true;
    // Main iteration loop
    while (new_input) {
      new_input = false;
      list_iter* cur_last(prev_inputs);
      for (tran_iter ifn = fn_begin; (ifn != fn_end); ++ifn) {
        combinations(*ifn, ifn->args().begin(), ifn->args().end(), 
                     cur_last, values, new_input);
        cur_last += ifn->args().size();
      }
    }
  }
}}

using namespace ceta::impl;


namespace ceta {
namespace cfg {
  class cfg_impl : boost::noncopyable {
  public:
    cfg_impl(void) {
    }
  
    symbol_t add_terminal(const char* id) {
      terminals_.push_back(symbol_impl(terminal, id, terminals_.size()));
      return &terminals_.back();
    }

    symbol_t add_nonterminal(const char* id) {
      nonterminals_.push_back(
              symbol_impl(nonterminal, id, nonterminals_.size()));
      return &nonterminals_.back();
    }

    void add_transition(const symbol_t* lhs_begin, const symbol_t* lhs_end,
                        symbol_t rhs) {
      tran_t t(lhs_begin, lhs_end, rhs);
      if (t.args().size() == 0) {
        cons_.push_back(t);
      } else {
        fns_.push_back(t);
      }
    }
    
    parikh_map_t parikh_image(void) const {
      // Compute base trees
      base_tree_list trees(nonterminals_);
      std::copy(cons_.begin(), cons_.end(),
                back_insert_iterator< base_tree_list >(trees));
  
      base_combinations(fns_.begin(), fns_.end(), trees);
      
      typedef list<symbol_impl>::const_iterator sym_iter;
      const sym_iter nt_begin = nonterminals_.begin();
      const sym_iter nt_end = nonterminals_.end();

      // Compute initial constants and periods.
      constant_list constants;
      for (sym_iter i = nt_begin; i != nt_end; ++i) {
        typedef base_tree_list::iterator iter;
  
        iter trees_begin(trees.begin(&*i));
        iter trees_end(trees.end(&*i));
  
        for (iter itree = trees_begin; itree != trees_end; ++itree) {
          if (itree->nonterminal_leaf_count() == zero)
            constants.insert(*itree);
        }
      }
  
      // Make list of periods
      vector<period> periods(trees.periods().begin(), trees.periods().end());

      // Compute all constants
      combinations(periods.begin(), periods.end(), constants);
  
      // Group all valid constants by root symbol and in_tree vectors
      typedef pair<symbol_t, const set<symbol_t> > constant_id; 
      typedef map<constant_id, list<base_tree> > constant_groups_t;
      constant_groups_t constant_groups;
      typedef constant_list::iterator con_iter;
      for (con_iter i(constants.begin()); i != constants.end(); ++i) {
        if (i->nonterminal_leaf_count() == zero) {
          constant_id id(i->root(), i->nonterminal_set());
          constant_groups[id].push_back(*i);
        }
      }
  
      // Group each period by the root state
      typedef vector<period>::iterator per_iter;
      map<symbol_t, list<period> > period_groups;
      for (per_iter i = periods.begin(); i != periods.end(); ++i)
        period_groups[i->root()].push_back(*i);
  
      const size_t terminal_count = terminals_.size();

      // Iterate through each state to initialize semilinear set for state
      map<symbol_t, semilinear_set> sets;
      for (sym_iter i = nonterminals_.begin(); i != nt_end; ++i)
        sets.insert(make_pair(&*i, semilinear_set(terminal_count)));

      typedef constant_groups_t::const_iterator g_iter;
      g_iter cg_begin = constant_groups.begin();
      g_iter cg_end = constant_groups.end();
      for (g_iter ig = cg_begin; ig != cg_end; ++ig) {
        symbol_t root = ig->first.first;
        const set<symbol_t>& in_tree = ig->first.second;
        const list<base_tree>& constants = ig->second;
  
        linear_set_group group(terminal_count);
  
        typedef list<base_tree>::const_iterator tree_iter;
        for (tree_iter i = constants.begin(); i != constants.end(); ++i) {
          unsigned c[terminal_count];
          std::fill(c, c + terminal_count, 0);
          initialize_vector(*i, c);
          group.insert_constant(c);
        }

        for (sym_iter in = nt_begin; in != nt_end; ++in) {
          if (in_tree.count(&*in) > 0) {
            const list<period>& periods(period_groups[&*in]);
             
            typedef list<period>::const_iterator period_iter;
            for (period_iter i = periods.begin(); i != periods.end(); ++i) {
              unsigned p[terminal_count];
              std::fill(p, p + terminal_count, 0);
              initialize_vector(*i, p);
              group.insert_period(p);
            }
          }
        }
        sets[root].insert(group);
      }
      return sets;
    }
  private:
    list<symbol_impl> terminals_;
    list<symbol_impl> nonterminals_;
    list<base_tree> cons_;
    list<tran_t> fns_;
  };
  

  cfg_t::cfg_t(void)
    : impl_(new cfg_impl()) {
  }
  
  cfg_t::~cfg_t(void) {
    delete impl_;
  }
  
  symbol_t cfg_t::add_terminal(const char* id) {
    return impl_->add_terminal(id);
  }
  
  symbol_t cfg_t::add_nonterminal(const char* id) {
    return impl_->add_nonterminal(id);
  }

  void cfg_t::add_transition(const symbol_t* lhs_begin,
          const symbol_t* lhs_end, symbol_t rhs) {
    impl_->add_transition(lhs_begin, lhs_end, rhs);
  }
  
  parikh_map_t cfg_t::parikh_image(void) const {
    return impl_->parikh_image();
  }
}
}

