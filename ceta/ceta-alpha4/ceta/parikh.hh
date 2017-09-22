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
    parikh_tree_t(const Nonterminal& root, size_t leaf)
      : impl_(new impl_t(root, false)) {
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
    bool has_been_pumped(void) const {
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
    std::vector<size_t> leaf_counts(size_t terminal_count) const {
      std::vector<size_t> result(terminal_count, 0);
      typedef std::map<size_t, size_t>::const_iterator iter;
      iter leaf_counts_end = impl_->leaf_counts.end();
      for (iter i = impl_->leaf_counts.begin(); i != leaf_counts_end; ++i)
        result[i->first] = i->second;
      return result;
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
    void add_leaf_counts(const std::map<size_t, size_t>& new_leafs) {
      typedef std::map<size_t, size_t>::const_iterator iter;
      for (iter i = new_leafs.begin(); i != new_leafs.end(); ++i)
        impl_->leaf_counts[i->first] += i->second;
    }

    /** Structure for storing details of nonterminal implementation. */
    struct impl_t {
      /** Constructs a new implementation record. */
      impl_t(const Nonterminal& root_arg,
             bool pumped_arg)
        : root(root_arg),
          pumped(pumped_arg) {
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
      /**
       * Maps terminals to number of occurances in leaf.
       * If a terminal is not in map, the leaf count is zero.
       */
      std::map<size_t, size_t> leaf_counts;
    };

    boost::shared_ptr<impl_t> impl_;
  };

  template<typename Nonterminal>
  std::ostream& operator<<(std::ostream& o,
                           const parikh_tree_t<Nonterminal>& tree) {
    o << "Root:   " << tree.root() << std::endl
      << "Pumped: " << (tree.has_been_pumped() ? "true" : "false")
      << std::endl
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
      << "}" << std::endl;
//      << "Leaf Counts: ["
//      << make_range_writer(tree.leaf_counts().begin(),
//                           tree.leaf_counts().end(), ", ")
//      << "]" << std::endl;
    return o;
  }

  /**
   * Data structure for storing trees constructed during computation of
   * Parikh image.  This data structure categorizes trees into several
   * different categories: base constants, pumped constants, contexts, and
   * periods.  A base constant tree does not have a terminal leaf,
   */
  template<typename Nonterminal>
  class parikh_tree_list_t {
    typedef std::vector< parikh_tree_t<Nonterminal> > tree_vector_t;
    typedef std::set<Nonterminal> branches_t;
    typedef std::set<branches_t> branch_set_t;
    /** Pair identifying roota and set of branches. */
    typedef std::pair<Nonterminal, branches_t> constant_pair_t;
    typedef std::map<Nonterminal, branch_set_t> branch_map_t;
    typedef std::map<constant_pair_t, tree_vector_t> constant_map_t;
    typedef std::map<Nonterminal, tree_vector_t> period_map_t;
  public:
    parikh_tree_list_t(void) {
    }

    /** Insert a Parikh tree into the list. */
    void insert(const parikh_tree_t<Nonterminal>& tree) {
      if (tree.nonterminal_leaf()) {
        // If period
        if (tree.root() == *tree.nonterminal_leaf()) {
          periods_[tree.root()].push_back(tree);
        } else { // Must be context
          base_.push_back(tree);
        }
      } else { // Must be constant
        if (!tree.has_been_pumped())
          base_.push_back(tree);
        pumped_.push_back(tree);
        branch_sets_[tree.root()].insert(tree.branches());
        constant_pair_t pair(tree.root(), tree.branches());
        constants_[pair].push_back(tree);
      }
    }

    /** Returns Parikh trees constants built up during basic generation. */
    const tree_vector_t& base(void) const {
      return base_;
    }

    /** Returns constant trees. */
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

  /**
   * A parameterized class designed to allow semi-incremental Parikh
   * construction in which new terminal symbols may be introduces along with
   * rules from terminating symbols to nonterminals.  This class requires
   * clients specify all of the unary and regular rules up front.
   *
   * For reasons of performance and implementation simplicity, this class
   * may wind up in an inconsistent state if one of the method calls fails
   * due to insufficient resources.  After an exception, we only guarantee
   * that the class will be destructable and will not leak resources.
   */
  template<typename Nonterminal>
  class parikh_constructor_t {
  public:
    template<typename NonterminalIterator, typename RuleIterator>
    parikh_constructor_t(NonterminalIterator nt_begin,
                         NonterminalIterator nt_end,
                         RuleIterator rules_begin,
                         RuleIterator rules_end)
      : nonterminals_(nt_begin, nt_end),
        terminal_count_(0),
        base_count_(0),
        pumped_count_(0) {
      // Create explorer for each rrule
      for (RuleIterator i = rules_begin; i != rules_end; ++i)
        rrules_.push_back(rrule_explorer_t(*i));
    }

    /** Adds a new terminal to the parikh sets. */
    template<typename NonterminalIterator>
    void add_terminal(NonterminalIterator nt_begin,
                      NonterminalIterator nt_end) {
      size_t new_index = terminal_count_;
      ++terminal_count_;

      for (NonterminalIterator i = nt_begin; i != nt_end; ++i)
        trees_.insert(parikh_tree_t<Nonterminal>(*i, new_index));

      // Perform base expansion.
      while (base_count_ != trees_.base().size()) {
        parikh_tree_t<Nonterminal> cur_tree = trees_.base()[base_count_];
        typedef typename rrule_explorers_t::iterator iter;
        for (iter i = rrules_.begin(); i != rrules_.end(); ++i)
          i->explore(trees_, cur_tree);
        ++base_count_;
      }

      // Apply periods to constants until completion.
      pumped_count_ = 0;
      while (pumped_count_ != trees_.pumped().size()) {
        parikh_tree_t<Nonterminal> cur_tree = trees_.pumped()[pumped_count_];
        period_explore(cur_tree);
        ++pumped_count_;
      }

    }

    std::map<Nonterminal, semilinear_set> image(void) const {
      typedef typename std::vector<Nonterminal>::const_iterator nt_iter;
      typedef std::vector< parikh_tree_t<Nonterminal> > tree_vector_t;
      typedef typename tree_vector_t::const_iterator tree_iter;

      // Build semilinear sets.
      std::map<Nonterminal, semilinear_set> result;
      // Iterate through nonterminals.
      nt_iter nt_end = nonterminals_.end();
      for (nt_iter i = nonterminals_.begin(); i != nt_end; ++i) {
        const Nonterminal& cur_nt = *i;

        // Create semilinear set we are going to build for cur_nt.
        semilinear_set& cur_set = result.insert(
           std::make_pair(cur_nt,
                          semilinear_set(terminal_count_))).first->second;
        // Get branch sets for current nonterminal.
        typedef std::set< std::set<Nonterminal> > branch_set_t;
        const branch_set_t& bset = trees_.branch_sets(cur_nt);

        // For each branch set.
        typedef typename branch_set_t::const_iterator branch_iter;
        for (branch_iter ib = bset.begin(); ib != bset.end(); ++ib) {
          // Create linear set group for branch set.
          linear_set_group group(terminal_count_);
          // Add constants for current nonterminal and branch set.
          const tree_vector_t& c = trees_.constants(cur_nt, *ib);
          for (tree_iter i = c.begin(); i != c.end(); ++i) {
            std::vector<size_t> leafc = i->leaf_counts(terminal_count_);
            group.insert_constant(&leafc[0]);
          }
          // Add periods for each nonterminal in branch set.
          typedef typename std::set<Nonterminal>::const_iterator nt_iter;
          nt_iter p_end = ib->end();
          for (nt_iter ip = ib->begin(); ip != p_end; ++ip) {
            const tree_vector_t& p = trees_.periods(*ip);
            for (tree_iter i = p.begin(); i != p.end(); ++i) {
              std::vector<size_t> leafc = i->leaf_counts(terminal_count_);
              group.insert_period(&leafc[0]);
            }
          }
          // Add group to semilinear set.
          cur_set.insert(group);
        }
      }
      return result;
    }
  private:
    typedef std::vector<parikh_tree_t<Nonterminal> > parikh_vector_t;

    /**
     * Expands a parikh_tree by a height of at most one using a rrule.
     * It attempts to add nonterminals as leafs to trees that do not already
     * have them, and combines two trees together.
     */
    class rrule_explorer_t {
    public:
      /** Construct a new rrule explorer given a rule and pointer to list. */
      rrule_explorer_t(const rrule_t<Nonterminal>& rule)
        : root_(rule.lhs),
          lhs_(rule.rhs1),
          rhs_(rule.rhs2) {
      }

      /**
       * Explore trees that have been added to list since last exploration.
       */
      void explore(parikh_tree_list_t<Nonterminal>& list,
                   const parikh_tree_t<Nonterminal>& tree) {
        typedef typename parikh_vector_t::const_iterator iter;
        bool root_in_tree = tree.branches().count(root_) > 0;
        bool tree_is_ground = !tree.nonterminal_leaf();
        // If the tree's root equals the left-hand-size of the rule.
        if (tree.root() == lhs_) {
          // Add tree "root_(tree, rhs_)" to list if is ground and
          if (tree_is_ground && (!root_in_tree || (root_ == rhs_)))
            list.insert(parikh_tree_t<Nonterminal>(root_, rhs_, tree));
          for (iter i = rhs_matches_.begin(); i != rhs_matches_.end(); ++i)
            explore(list, tree, *i);
          lhs_matches_.push_back(tree);
        }
        if (tree.root() == rhs_) {
          if (tree_is_ground && (!root_in_tree || (root_ == lhs_)))
            list.insert(parikh_tree_t<Nonterminal>(root_, lhs_, tree));
          for (iter i = lhs_matches_.begin(); i != lhs_matches_.end(); ++i) {
            explore(list, *i, tree);
          }
          rhs_matches_.push_back(tree);
        }
      }
    private:
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
        if (valid)
          list.insert(parikh_tree_t<Nonterminal>(root_, lhs, rhs));
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

    /** Consider expanding tree by adding period to tree. */
    void period_explore(const parikh_tree_t<Nonterminal>& tree) {
      // Get nonterminals for tree.
      typedef std::set<Nonterminal> nt_set_t;
      const nt_set_t& nt_set = tree.branches();

      // Iterate through each nonterminal in tree.
      typedef typename nt_set_t::const_iterator nt_iter;
      for (nt_iter i = nt_set.begin(); i != nt_set.end(); ++i) {
        // Get periods with root equal to current nonterminal.
        typedef std::vector<parikh_tree_t<Nonterminal> > tree_vector_t;
        const tree_vector_t& periods = trees_.periods(*i);
        // Iterate through each period.
        typedef typename tree_vector_t::const_iterator v_iter;
        for (v_iter ip = periods.begin(); ip != periods.end(); ++ip) {
          // Check that period would add new nonterminal to tree.
          if (!subset(ip->branches(), nt_set))
            trees_.insert(parikh_tree_t<Nonterminal>(tree, *ip));
        }
      }
    }

    std::vector<Nonterminal> nonterminals_;
    typedef std::vector<rrule_explorer_t> rrule_explorers_t;
    rrule_explorers_t rrules_;
    size_t terminal_count_;
    parikh_tree_list_t<Nonterminal> trees_;
    /** Number of trees in base list that have been explored. */
    size_t base_count_;
    /** Number of trees in pumped list that have been explored. */
    size_t pumped_count_;
  };

  /**
   * Computes the parikh image of every non-terminal symbol in the grammar.
   */
  template<typename Nonterminal>
  std::map<Nonterminal, semilinear_set>
  parikh_image(size_t terminal_count, const cfg_t<size_t, Nonterminal>& g) {

    typedef typename cfg_t<size_t,Nonterminal>::nonterminal_iterator nt_iter;
    typedef typename cfg_t<size_t,Nonterminal>::trule_iterator trule_iter;
    typedef typename cfg_t<size_t,Nonterminal>::urule_iterator urule_iter;
    typedef typename cfg_t<size_t,Nonterminal>::rrule_iterator rrule_iter;
    typedef std::vector<parikh_tree_t<Nonterminal> > tree_vector_t;
    typedef typename tree_vector_t::const_iterator tree_iter;

    // Maps each nonterminal to the nonterminals that it can reach via
    // epsilon transitions.
    typedef std::map<Nonterminal, std::set<Nonterminal> > urule_map_t;
    urule_map_t urule_map;
    for (urule_iter i = g.urules_begin(); i != g.urules_end(); ++i)
      urule_map[i->rhs].insert(i->lhs);

    // Create explorer for each rrule
    std::vector< rrule_t<Nonterminal> > rrules;
    for (rrule_iter i = g.rrules_begin(); i != g.rrules_end(); ++i) {
      Nonterminal rhs1 = i->rhs1;
      Nonterminal rhs2 = i->rhs2;
      std::set<Nonterminal>& lhs_set = urule_map[i->lhs];
      lhs_set.insert(i->lhs);
      typedef typename std::set<Nonterminal>::const_iterator iter;
      for (iter i = lhs_set.begin(); i != lhs_set.end(); ++i)
        rrules.push_back(rrule_t<Nonterminal>(*i, rhs1, rhs2));
    }

    parikh_constructor_t<Nonterminal> pc(g.nonterminals_begin(),
            g.nonterminals_end(), rrules.begin(), rrules.end());

    typedef std::vector< std::set<Nonterminal> > trules_t;
    trules_t trules(terminal_count);
    for (trule_iter i = g.trules_begin(); i != g.trules_end(); ++i)
      trules[i->rhs].insert(i->lhs);

    typedef typename trules_t::const_iterator trules_iter;
    for (trules_iter i = trules.begin(); i != trules.end(); ++i)
      pc.add_terminal(i->begin(), i->end());

    return pc.image();
  }
}
}

#endif
