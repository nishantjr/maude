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
#ifndef _parikh_hh_
#define _parikh_hh_
/** \file
 * A datastructure for context free grammars and algorithm for computing
 * its Parikh image.
 *
 * TODO: Enhance Parikh image construction so that we do not expand trees
 * using unary rules explicitly, but rely on an reachability relation.
 */

#include <map>

#include <boost/shared_ptr.hpp>
#include <boost/optional/optional.hpp>

#include "cfg.hh"
#include "sls.hh"
#include "writer.hh"

namespace ceta {

/** Namespace for context free grammar and related classes. */
namespace cfg {
  template<typename Nonterminal>
  class parikh_tree_t {
  public:
    /**
     * Construct a parikh tree with a single terminal leaf and nonterminal
     * root.
     */
    parikh_tree_t(size_t terminal_count,
                  const Nonterminal& root,
                  size_t leaf)
      : impl_(new impl_t(terminal_count, root, false)) {
      impl_->in_tree.insert(root);
      impl_->leaf_counts[leaf] = 1;
    }

    /**
     * Constructs a parikh tree with the given root and a single parikh tree
     * as its child.
     */
    parikh_tree_t(const Nonterminal& root,
                  const parikh_tree_t<Nonterminal>& child)
      : impl_(new impl_t(*child.impl_)) {
      set_root(root);
    }

    /**
     * Constructs a parikh tree with the given root and two children, one
     * of which is a nonterminal leaf and the other of which is a parikh
     * tree.
     */
    parikh_tree_t(const Nonterminal& root,
                  const Nonterminal& child1,
                  const parikh_tree_t<Nonterminal>& child2)
      : impl_(new impl_t(*child2.impl_)) {
      set_root(root);
      set_nonterminal_leaf(child1);
    }
    /**
     * Constructs a parikh tree with the given root and two Parikh trees
     * as children.
     */
    parikh_tree_t(const Nonterminal& root,
                  const parikh_tree_t<Nonterminal>& child1,
                  const parikh_tree_t<Nonterminal>& child2)
      : impl_(new impl_t(*child1.impl_)) {
      set_root(root);
      if (child2.impl_->nonterminal_leaf)
        set_nonterminal_leaf(*child2.impl_->nonterminal_leaf);
      impl_->in_tree.insert(child2.impl_->in_tree.begin(),
                            child2.impl_->in_tree.end());
      add_leaf_counts(child2.impl_->leaf_counts);
    }

    /** Constructs a Parikh tree by adding a period to a constant. */
    parikh_tree_t(const parikh_tree_t<Nonterminal>& constant,
                  const parikh_tree_t<Nonterminal>& period)
      : impl_(new impl_t(*constant.impl_)) {
      impl_->pumped = true;
      impl_->in_tree.insert(period.impl_->in_tree.begin(),
                            period.impl_->in_tree.end());
      add_leaf_counts(period.impl_->leaf_counts);
    }

    /** Returns root symbol of tree. */
    const Nonterminal& root(void) const {
      return impl_->root;
    }

    /**
     * Returns true if this tree has been constructed by adding a period to a
     * base tree.
     */
    bool pumped(void) const {
      return impl_->pumped;
    }

    /** Returns nonterminal appearing in a leaf if any. */
    const boost::optional<Nonterminal>& nonterminal_leaf(void) const {
      return impl_->nonterminal_leaf;
    }

    /** Returns set of nonterminals appearing in branches. */
    const std::set<Nonterminal>& branches(void) const {
      if (impl_ == NULL)
        throw std::logic_error("Unassigned implementation");
      return impl_->in_tree;
    }

    /** Returns number of occurances of each terminal in leaf. */
    const std::vector<size_t>& leaf_counts(void) const {
      return impl_->leaf_counts;
    }
  private:
    /** Sets root of tree and adds as branch. */
    void set_root(const Nonterminal& root) {
      impl_->root = root;
      impl_->in_tree.insert(root).second;
    }

    /** Sets nonterminal leaf of this tree. */
    void set_nonterminal_leaf(const Nonterminal& leaf) {
      if (impl_->nonterminal_leaf)
        throw std::logic_error("Only one nonterminal leaf permitted.");
      impl_->nonterminal_leaf = leaf;
    }

    /** Add vector to leafs counts of this tree. */
    void add_leaf_counts(const std::vector<size_t>& v) {
      if (impl_->leaf_counts.size() != v.size())
        throw std::logic_error(
            "Number of terminal symbols do not match.");
      std::vector<size_t>::iterator cur_leaf = impl_->leaf_counts.begin();
      typedef std::vector<size_t>::const_iterator leaf_iter;
      leaf_iter v_end   = v.end();
      for (leaf_iter i = v.begin(); i != v_end; ++i, ++cur_leaf)
        *cur_leaf += *i;
    }

    /** Structure for storing details of nonterminal implementation. */
    struct impl_t {
      /** Constructs a new implementation record. */
      impl_t(size_t nonterminal_count,
             const Nonterminal& root_arg,
             bool pumped_arg)
        : root(root_arg),
          pumped(pumped_arg),
          leaf_counts(nonterminal_count, 0) {
      };

      /** Root symbol of tree. */
      Nonterminal root;
      /**
       * Indicates if this tree has been constructed by adding a period to a
       * base tree.
       */
      bool pumped;
      /** Nonterminal appearing in a leaf if any. */
      boost::optional<Nonterminal> nonterminal_leaf;
      /** Set of nonterminals appearing in branches. */
      std::set<Nonterminal> in_tree;
      /** Number of occurances of each terminal in leaf. */
      std::vector<size_t> leaf_counts;
    };

    boost::shared_ptr<impl_t> impl_;
  };

  template<typename Nonterminal>
  std::ostream& operator<<(std::ostream& o,
                           const parikh_tree_t<Nonterminal>& tree) {
    o << "Root:   " << tree.root() << std::endl
      << "Pumped: " << (tree.pumped() ? "true" : "false") << std::endl
      << "Nonterminal Leaf: ";
    if (tree.nonterminal_leaf()) {
      o << *tree.nonterminal_leaf();
    } else {
      o << "none";
    }
    o << std::endl
      << "Branches: {"
      << make_range_writer(tree.branches().begin(),
                           tree.branches().end(), ", ")
      << "}" << std::endl
      << "Leaf Counts: ["
      << make_range_writer(tree.leaf_counts().begin(),
                           tree.leaf_counts().end(), ", ")
      << "]" << std::endl;

    return o;
  }

  /** List of trees constructed during computation of Parikh image. */
  template<typename Nonterminal>
  class parikh_tree_list_t {
    typedef std::vector< parikh_tree_t<Nonterminal> > tree_vector_t;
    typedef std::set<Nonterminal> branches_t;
    typedef std::set<branches_t> branch_set_t;
    /**
     * A pair identifying a nonterminal as root symbol and set of
     * branches.
     */
    typedef std::pair<Nonterminal, branches_t> constant_pair_t;
    typedef std::map<Nonterminal, branch_set_t> branch_map_t;
    typedef std::map<constant_pair_t, tree_vector_t> constant_map_t;
    typedef std::map<Nonterminal, tree_vector_t> period_map_t;
  public:
    /** Insert a Parikh tree into the list. */
    void insert(const parikh_tree_t<Nonterminal>& tree) {
      if (tree.nonterminal_leaf()) {
        // If period
        if (tree.root() == *tree.nonterminal_leaf()) {
          periods_[tree.root()].push_back(tree);
        } else { // Must be context
          contexts_.push_back(tree);
        }
      } else { // Must be constant
        if (tree.pumped()) {
          pumped_.push_back(tree);
        } else {
          base_.push_back(tree);
        }
        branch_sets_[tree.root()].insert(tree.branches());
        constant_pair_t pair(tree.root(), tree.branches());
        constants_[pair].push_back(tree);
      }
    }

    /** Returns Parikh trees constants built up during basic generation. */
    const tree_vector_t& base(void) const {
      return base_;
    }

    /**
     * Returns Parikh tree constants built by adding one or more periods to
     * a base tree.
     */
    const tree_vector_t& pumped(void) const {
      return pumped_;
    }

    /**
     * Returns the sets of nonterminals that are the branch set of a Parikh
     * tree with given root nonterminal.
     */
    const branch_set_t& branch_sets(const Nonterminal& root) const {
      typename branch_map_t::const_iterator i = branch_sets_.find(root);
      return (i != branch_sets_.end()) ? i->second : empty_set_;
    }

    /**
     * Returns Parikh tree constants that have given root and set of
     * branches.
     */
    const tree_vector_t&
    constants(const Nonterminal& root, const branches_t& branches)
    const {
      typedef typename constant_map_t::const_iterator iter;
      iter i = constants_.find(constant_pair_t(root, branches));
      return (i != constants_.end()) ? i->second : empty_vector_;
    }

    /**
     * Returns Parikh trees that have a nonterminal leaf and are not periods.
     */
    const tree_vector_t& contexts(void) const {
      return contexts_;
    }

    /** Returns Parikh tree periods with given root. */
    const tree_vector_t& periods(const Nonterminal& root) const {
      typename period_map_t::const_iterator i = periods_.find(root);
      return (i != periods_.end()) ? i->second : empty_vector_;
    }
  private:
    /** Base constant trees constructed so far. */
    tree_vector_t base_;
    /** Pumped constant trees constructed so far. */
    tree_vector_t pumped_;
    /**
     * Mapping from each nonterminal to the set of branch sets of constants
     * with given nonterminal as a root.
     */
    branch_map_t branch_sets_;
    /** Mapping from constant pair to constants matching that pair. */
    constant_map_t constants_;
    /** Context trees constructed so far. */
    tree_vector_t contexts_;
    /** Mapping from nonterminal to periods with that nonterminal as root. */
    period_map_t periods_;
    /** Empty set that is returned as default when needed. */
    const branch_set_t empty_set_;
    /** Empty vector that is returned as default when needed. */
    const tree_vector_t empty_vector_;
  };

  /** Consider expanding tree by adding new urule to top. */
  template<typename Nonterminal>
  void urule_explore(parikh_tree_list_t<Nonterminal>& list,
                     const urule_t<Nonterminal>& rule,
                     const parikh_tree_t<Nonterminal>& tree) {
    // Check if rule lhs does not appear in cur_tree as branch.
    bool lhs_not_branch = tree.branches().count(rule.lhs) == 0;
    if (lhs_not_branch && (tree.root() == rule.rhs))
      list.insert(parikh_tree_t<Nonterminal>(rule.lhs, tree));
  }

  /**
   * Expands a parikh_tree by a height of at most one using a rrule.
   * It attempts to add nonterminals as leafs to trees that do not already
   * have them, and combines two trees together.
   */
  template<typename Nonterminal>
  class rrule_explorer_t {
  public:
    /** Construct a new rrule explorer given a rule and pointer to list. */
    rrule_explorer_t(const rrule_t<Nonterminal>& rule)
      : root_(rule.lhs),
        lhs_(rule.rhs1),
        rhs_(rule.rhs2) {
    }

    /** Explore trees that have been added to list since last exploration. */
    void explore(parikh_tree_list_t<Nonterminal>& list,
                 const parikh_tree_t<Nonterminal>& tree) {
      typedef typename parikh_vector_t::const_iterator iter;
      bool root_in_tree = tree.branches().count(root_) > 0;
      if (tree.root() == lhs_) {
        if (!tree.nonterminal_leaf() && (!root_in_tree || (root_ == rhs_)))
          list.insert(parikh_tree_t<Nonterminal>(root_, rhs_, tree));
        for (iter i = rhs_matches_.begin(); i != rhs_matches_.end(); ++i)
          explore(list, tree, *i);
        lhs_matches_.push_back(tree);
      }
      if (tree.root() == rhs_) {
        if (!tree.nonterminal_leaf() && (!root_in_tree || (root_ == lhs_)))
          list.insert(parikh_tree_t<Nonterminal>(root_, lhs_, tree));
        for (iter i = lhs_matches_.begin(); i != lhs_matches_.end(); ++i) {
          explore(list, *i, tree);
        }
        rhs_matches_.push_back(tree);
      }
    }
  private:
    typedef std::vector<parikh_tree_t<Nonterminal> > parikh_vector_t;

    /** Make trees using new combinations from lhs and rhs. */
    void explore(parikh_tree_list_t<Nonterminal>& list,
                 const parikh_tree_t<Nonterminal>& lhs,
                 const parikh_tree_t<Nonterminal>& rhs) {
      bool valid = false;
      bool root_in_lhs = lhs.branches().count(root_) > 0;
      bool root_in_rhs = rhs.branches().count(root_) > 0;
      if (lhs.nonterminal_leaf()) {
        valid = !rhs.nonterminal_leaf() && !root_in_rhs
            && (!root_in_lhs || (root_ == *lhs.nonterminal_leaf()));
      } else if (rhs.nonterminal_leaf()) {
        valid = !root_in_lhs
            && (!root_in_rhs || (root_ == *rhs.nonterminal_leaf()));
      } else {
        valid = !root_in_lhs && !root_in_rhs;
      }
      if (valid) {
        list.insert(parikh_tree_t<Nonterminal>(root_, lhs, rhs));
      }
    }
    /** Root of trees formed. */
    Nonterminal root_;
    /** First argument of rule. */
    Nonterminal lhs_;
    /** Parikh trees that reach first arg of rule. */
    parikh_vector_t lhs_matches_;
    /** Second argument of rule. */
    Nonterminal rhs_;
    /** Parikh trees that reach second arg of rule. */
    parikh_vector_t rhs_matches_;
  };

  /** Returns true if x is a subset of y. */
  template <typename E>
  bool subset(const std::set<E>& x, const std::set<E>& y) {
    typedef typename std::set<E>::const_iterator iter;
    iter x_end = x.end();
    bool result = true;
    for (iter i = x.begin(); result && (i != x_end); ++i)
      result = (y.count(*i) > 0);
    return result;
  }

  /** Try exploring tree using base techniques. */
  template<typename Nonterminal, typename Iurule, typename IRex>
  void base_explore(Iurule u_begin, Iurule u_end,
                    IRex r_begin, IRex r_end,
                    parikh_tree_list_t<Nonterminal>& list,
                    const parikh_tree_t<Nonterminal> tree) {
    for (Iurule i = u_begin; i != u_end; ++i)
      urule_explore(list, *i, tree);
    for (IRex i = r_begin; i != r_end; ++i) {
      i->explore(list, tree);
    }
  }

  /** Consider expanding tree by adding period to tree. */
  template<typename Nonterminal>
  void period_explore(parikh_tree_list_t<Nonterminal>& list,
                      const parikh_tree_t<Nonterminal>& tree) {
    // Get nonterminals for tree.
    typedef std::set<Nonterminal> nt_set_t;
    const nt_set_t& nt_set = tree.branches();

    // Iterate through each nonterminal in tree.
    typedef typename nt_set_t::const_iterator nt_iter;
    for (nt_iter i = nt_set.begin(); i != nt_set.end(); ++i) {
      // Get periods with root equal to current nonterminal.
      typedef std::vector<parikh_tree_t<Nonterminal> > tree_vector_t;
      const tree_vector_t& periods = list.periods(*i);
      // Iterate through each period.
      typedef typename tree_vector_t::const_iterator v_iter;
      for (v_iter ip = periods.begin(); ip != periods.end(); ++ip) {
        // Check that period would add new nonterminal to tree.
        if (!subset(ip->branches(), nt_set))
          list.insert(parikh_tree_t<Nonterminal>(tree, *ip));
      }
    }
  }

  //NOTE: This has been commented out in the hopes that one day I will
  // start using this approach.
  /**
   * A parameterized class designed to allow semi-incremental Parikh
   * construction in which new terminal symbols may be introduces along with
   * rules from terminating symbols to nonterminals.  This class requires
   * clients specify all of the unary and regular rules up front.
   *
   * For reasons of performance and implementation simplicity, this class
   * may wind up in an inconsistent state if one of the method calls fail due
   * to insignificant resources.  After an exception, we only guarantee that
   * the class will be destructable and will not leak resources.
   */
  //template<typename Nonterminal>
  //class parikh_constructor_t {
  //  template<typename Iurule, typename Irrule>
  //  parikh_constructor_t(Iurule urule_begin, Iurule urule_end,
  //                       Irrule rrule_begin, Irrule rrule_end)
  //    : urules_(urule_begin, urule_end),
  //      terminal_count_(0) {
  //  }

  //  void set_terminal_count(size_t count) {
  //  }
  //  void add(const trule_t<Nonterminal>& rule) {
  //  }

  //  /** Resets the list of nonterminals that have changed. */
  //  void reset(void) {
  //  }

  //  /**
  //   * Returns the nonterminals whose semilinear sets are different since
  //   * the last time reset() was called.
  //   */
  //  const std::set<Nonterminal>& changes(void) const {
  //  }
  //  const semilinear_set& image(const Nonterminal& nt) const {
  //  }
  //private:
  //  const std::vector<urule_t<Nonterminal> > urules_;
  //  std::vector<rrule_explorer<Nonterminal> > rrules_;
  //  size_t terminal_count_;
  //  mutable parikh_tree_list_t<Nonterminal> trees_;
  //  mutable size_t base_constant_count_;
  //  mutable std::map<Nonterminal, semilinear_set> map_;
  //};

  /**
   * Computes the parikh image of every non-terminal symbol in the grammar.
   */
  template<typename Nonterminal>
  std::map<Nonterminal, semilinear_set>
  parikh_image(size_t terminal_count, const cfg_t<size_t, Nonterminal>& g) {
    parikh_tree_list_t<Nonterminal> trees;

    typedef typename cfg_t<size_t,Nonterminal>::nonterminal_iterator nt_iter;
    typedef typename cfg_t<size_t,Nonterminal>::trule_iterator trule_iter;

    // Add base tree for each trule.
    for (trule_iter i = g.trules_begin(); i != g.trules_end(); ++i)
      trees.insert(
          parikh_tree_t<Nonterminal>(terminal_count, i->lhs, i->rhs));

    typedef std::vector< rrule_explorer_t<Nonterminal> > rex_t;
    // Create explorer for each rrule
    rex_t rrules;
    typedef typename cfg_t<size_t,Nonterminal>::rrule_iterator rrule_iter;
    for (rrule_iter i = g.rrules_begin(); i != g.rrules_end(); ++i)
      rrules.push_back(rrule_explorer_t<Nonterminal>(*i));

    // Build base trees where states do not appear multiple times in branch.
    size_t base_count = 0;
    size_t context_count = 0;
    while ((   base_count != trees.base().size())
        || (context_count != trees.contexts().size())) {
      // Explore new base.
      if (base_count != trees.base().size()) {
        base_explore(g.urules_begin(), g.urules_end(),
                     rrules.begin(), rrules.end(),
                     trees, trees.base()[base_count]);
        ++base_count;
      }

      // Explore new context
      if (context_count != trees.contexts().size()) {
        base_explore(g.urules_begin(), g.urules_end(),
                     rrules.begin(), rrules.end(),
                     trees, trees.contexts()[context_count]);
        ++context_count;
      }
    }

    typedef std::vector<parikh_tree_t<Nonterminal> > tree_vector_t;
    typedef typename tree_vector_t::const_iterator tree_iter;
    // Apply periods to bases.
    tree_iter base_end = trees.base().end();
    for (tree_iter ib = trees.base().begin(); ib != base_end; ++ib)
      period_explore(trees, *ib);
    // Apply periods to pumped trees until completion.
    size_t pumped_count = 0;
    while (pumped_count != trees.pumped().size()) {
      parikh_tree_t<Nonterminal> cur_tree = trees.pumped()[pumped_count];
      period_explore(trees, cur_tree);
      ++pumped_count;
    }

    // Build semilinear sets.
    std::map<Nonterminal, semilinear_set> result;
    // Iterate through nonterminals.
    nt_iter nt_end = g.nonterminals_end();
    for (nt_iter i = g.nonterminals_begin(); i != nt_end; ++i) {
      const Nonterminal& cur_nt = *i;

      // Create semilinear set we are going to build for current nonterminal.
      semilinear_set& cur_set = result.insert(
          make_pair(cur_nt, semilinear_set(terminal_count))).first->second;
      // Get branch sets for current nonterminal.
      typedef std::set< std::set<Nonterminal> > branch_set_t;
      const branch_set_t& bset = trees.branch_sets(cur_nt);

      // For each branch set.
      typedef typename branch_set_t::const_iterator branch_iter;
      for (branch_iter ib = bset.begin(); ib != bset.end(); ++ib) {
        // Create linear set group for branch set.
        linear_set_group group(terminal_count);
        // Add constants for current nonterminal and branch set.
        const tree_vector_t& c = trees.constants(cur_nt, *ib);
        for (tree_iter i = c.begin(); i != c.end(); ++i)
          group.insert_constant(&i->leaf_counts()[0]);
        // Add periods for each nonterminal in branch set.
        typedef typename std::set<Nonterminal>::const_iterator nt_iter;
        nt_iter p_end = ib->end();
        for (nt_iter ip = ib->begin(); ip != p_end; ++ip) {
          const tree_vector_t& p = trees.periods(*ip);
          for (tree_iter i = p.begin(); i != p.end(); ++i)
           group.insert_period(&i->leaf_counts()[0]);
        }
        // Add group to semilinear set.
        cur_set.insert(group);
      }
    }
    return result;
  }
}
}

#endif
