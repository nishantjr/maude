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
#ifndef _learncfg_hh_
#define _learncfg_hh_
//Future work: Consider other techniques to show every valid combination has
// been returned.  Ideas include: (1) Noting that all subsets with
// reducible state are essentially the same and that every string above a
// certain length must be reducible; (2) Checking that every "interesting"
// combination of states on the rhs of a rule has been returned.  A
// combination of states is interesting if it is not equivalent another
// subset of states when viewed by some other symbol.
// - Can I guarantee finding an accepting tree if one exists?

#include <deque>
#include <map>
#include <set>
#include <utility>

#include <boost/none.hpp>
#include <boost/optional/optional.hpp>
#include <boost/variant.hpp>

#include "earley.hh"
#include "learn.hh"
#include "writer.hh"

/** Base namespace for Ceta. */
namespace ceta {
/** Namespace for Context-free related declarations. */
namespace cfg {
  using ceta::fa::cons_list_t;
  using ceta::fa::decision_tree_t;

  /**
   * A reachable set of DFA nodes.  There are two sets of nodes: primary
   * nodes are those that we started in during exploration; secondary
   * nodes are those added when a primary DFA accepted.  There is guaranteed
   * to be exactly one primary node per nonterminal, but we may be in any
   * number of secondary nodes per nonterminal.
   *
   * The only purpose of this data structure is to determine when a set of
   * nodes is unique.  Consequentally, there is a partial order over subsets,
   * but no ability to determine which nodes are in the subset.
   */
  template<typename Nonterminal>
  class eq_subset_t {
  public:
    /**
     * Sets the primary state for a nonterminal. Note that there can be
     * at most one primary state for each nonterminal.  This function
     * overrides a previous assignment.
     */
    void add_primary(const std::pair<Nonterminal, size_t>& node) {
      primary_.insert(node);
    }
    /**
     * Adds a secondary state for a nonterminal.  There may be multiple
     * secondary states for each nonterminal.
     */
    void add_secondary(const std::pair<Nonterminal, size_t>& node) {
      secondary_.insert(node);
    }

    /** Defines < to be a strict total order over subsets. */
    bool operator<(const eq_subset_t<Nonterminal>& rhs) const {
      return (primary_ <  rhs.primary_)
          || (primary_ == rhs.primary_) && (secondary_ < rhs.secondary_);
    }
  private:
    /** Map from nonterminal to secondary nodes for nonterminal. */
    std::map<Nonterminal, size_t> primary_;
    /** Set of secondary nodes. */
    std::set< std::pair<Nonterminal, size_t> > secondary_;
  };

  /** Decision tree wrapper for cfg work. */
  template<typename Terminal, typename Nonterminal>
  class cfg_tree_t {
    typedef earley_trace_t<Nonterminal> trace_t;
    typedef chomsky_rules_t<Nonterminal> rules_t;
    typedef std::map<Terminal, std::set<Nonterminal> > trules_t;
    typedef std::pair<std::vector<Terminal>, trace_t> leaf_t;
    typedef decision_tree_t<leaf_t, cons_list_t<Terminal> > dtree_t;

  public:
    /** Constructs a new decision tree wrapper. */
    cfg_tree_t(const rules_t& rules,
               const trules_t& trules,
               const Nonterminal& nt,
               const trace_t& initial)
      : rules_(rules),
        trules_(trules),
        nt_(nt),
        dtree_(leaf_t(std::vector<Terminal>(), initial)) {
      // Get followups for nonterminal.
      typedef std::map<Nonterminal, std::set<Nonterminal> > nt_set_map_t;
      const nt_set_map_t& map = rules.followups(nt);

      // For each set in right-hand-side of map.
      typedef typename nt_set_map_t::const_iterator iter;
      for (iter i = map.begin(); i != map.end(); ++i)
        followups_.insert(i->second.begin(), i->second.end());
    }

    /** Returns nonterminal the tree is associated to. */
    const Nonterminal& nonterminal(void) const {
      return nt_;
    }

    /** Return true if decision tree for nonterminal has a single leaf. */
    size_t size(void) const {
      return dtree_.size();
    }

    /** Returns true if this node is a leaf. */
    bool is_leaf(size_t node) const {
      return dtree_.is_leaf(node);
    }

    /** Returns path leading up to leaf. */
    const std::vector<Terminal>& leaf_path(size_t leaf) const {
      return dtree_.leaf_label(leaf).first;
    }

    /** Returns the distinguisher associated with a branch node. */
    const cons_list_t<Terminal>& distinguisher(size_t branch) const {
      return dtree_.branch_label(branch);
    }

    /** Returns accepting child of branch. */
    size_t accept_child(size_t branch) const {
      return dtree_.accept_child(branch);
    }

    /** Returns rejecting child of branch. */
    size_t reject_child(size_t branch) const {
      return dtree_.reject_child(branch);
    }

    /** Returns index of initial node in tree. */
    size_t initial(void) const {
      return dtree_.initial();
    }

    /**
     * Converts leaf into branch.
     * @param leaf Leaf to convert into branch.
     * @param d Distinguisher for new branch.
     * @param leaf_accepts Indicates if leaf should be moved to accepting
     *                     branch (otherwise it moves to rejecting branch).
     * @param new_leaf The trace to label the new leaf with.
     */
    void make_branch(size_t leaf, const cons_list_t<Terminal>& d,
                     bool leaf_accepts,
                     const std::vector<Terminal>& new_path,
                     const trace_t& new_leaf) {
      dtree_.make_branch(leaf, d, leaf_accepts,
                         leaf_t(new_path, new_leaf));
    }

    /**
     * Returns the index of the DFA node we will be in if the node in the
     * given nonterminal reads t.
     */
    size_t next_node(size_t node, const Terminal& t) const {
      // Get Earley trace for current node.
      earley_trace_t<Nonterminal> trace = dtree_.leaf_label(node).second;
      // Advance parse.
      typedef std::set< std::pair<size_t, Nonterminal> > generated_set_t;
      const std::set<Nonterminal>& found = trules_.find(t)->second;
      generated_set_t gen = parse(rules_, trace, found.begin(), found.end());
      // See if parse accepts.
      bool accepts = gen.count(std::make_pair(0, nt_));
      // Get representative.
      return find_node(trace, accepts);
    }

    /**
     * Returns representative node in decision tree for given trace.
     *
     * @param trace trace to find representative for.
     * @param trace_accepts True if trace accepts the empty string.
     */
    size_t find_node(const trace_t& trace, bool accepts) const {
      return dtree_.find_rep(pred_t(*this, trace, accepts));
    }

    /**
     * Returns a pair identifying the lowest common ancestor to node1 and 2
     * and whether node1 is along accepting path from ancestor.
     */
    std::pair<size_t, bool> separator(size_t node1, size_t node2) const {
      typedef std::vector<size_t> path_t;
      path_t path1 = dtree_.path(node1);
      path_t path2 = dtree_.path(node2);

      // Iterate in reverse order (oldest first) until first difference.
      typedef path_t::const_reverse_iterator path_iter;
      path_iter i1 = path1.rbegin();
      path_iter i2 = path2.rbegin();
      while (*i1 == *i2) {
        ++i1;
        ++i2;
      }
      size_t common = dtree_.parent(*i1);
      bool accept = dtree_.accept_child(common) == *i1;
      return std::make_pair(common, accept);
    }

    /**
     * Return nonterminals that occur in rhs of rule after nt for this
     * tree.
     */
    const std::set<Nonterminal>& followups(void) const {
      return followups_;
    }

    /**
     * Return the appropriate child of branch based on how trace is
     * distinguished.
     */
    size_t pick_child(size_t branch,
                      const trace_t& trace,
                      bool empty_accepts) const {
      return accept_extension(trace, empty_accepts, distinguisher(branch))
           ? accept_child(branch)
           : reject_child(branch);
    }
  private:
    /**
     * Returns true if the trace accepts the nonterminal after reading
     * distinguisher (which must be non-empty).
     */
    bool accept_extension(const trace_t& trace,
                          bool empty_accepts,
                          const cons_list_t<Terminal>& distinguisher) const {
      if (distinguisher.empty()) {
        return empty_accepts;
      } else {
        trace_t cur_trace = trace;
        typedef std::set< std::pair<size_t, Nonterminal> > generated_set_t;
        generated_set_t gen;
        cons_list_t<Terminal> d = distinguisher;
        while (!d.empty()) {
          const std::set<Nonterminal>& found
                  = trules_.find(d.first())->second;
          gen = parse(rules_, cur_trace, found.begin(), found.end());
          d = d.rest();
        }
        return gen.count(std::make_pair(0, nt_)) > 0;
      }
    }

    class pred_t {
    public:
      /** Construct a new trace predicate. */
      pred_t(const cfg_tree_t<Terminal, Nonterminal>& tree,
             const trace_t& trace,
             bool empty_accepts)
        : tree_(tree),
          trace_(trace),
          empty_accepts_(empty_accepts) {
      }

      /**
       * Returns true if this trace generates the given terminal when the
       * distinguisher is added to it.
       */
      bool operator()(const cons_list_t<Terminal>& distinguisher) const {
        return tree_.accept_extension(trace_, empty_accepts_, distinguisher);
      }
    private:
      const cfg_tree_t& tree_;
      /** Trace to start parsing from. */
      const trace_t& trace_;
      /** True if the empty string is accepted by this trace. */
      bool empty_accepts_;
    };

    /** Reference to rules for current tree. */
    const rules_t& rules_;
    /** Reference to terminal rules for current tree. */
    const trules_t& trules_;
    /** Set of nonterminals we should start searching for if this accepts. */
    std::set<Nonterminal> followups_;
    /** Nonterminal tree is associated to. */
    Nonterminal nt_;
    /** Underlying decision tree. */
    dtree_t dtree_;
  };

  /** Writes some elements of tree to stream for debugging purposes. */
  template<typename Terminal, typename Nonterminal>
  std::ostream& operator<<(std::ostream& o,
                           const cfg_tree_t<Terminal, Nonterminal>& tree) {
    for (size_t i = 0; i != tree.size(); ++i) {
      o << i << ": ";
      if (tree.is_leaf(i)) {
        o << "leaf "
          << make_range_writer(tree.leaf_path(i).begin(),
                               tree.leaf_path(i).end(), "");
      } else {
        o << "branch dist: " << tree.distinguisher(i)
          << " accept: " << tree.accept_child(i)
          << " reject: " << tree.reject_child(i);
      }
      o << std::endl;
    }
    return o;
  }

  template<typename Terminal, typename Nonterminal>
  class cfg_tree_map_t {
  public:
    /** Type of rules for tree map. */
    typedef chomsky_rules_t<Nonterminal> rules_t;
    typedef std::map< Terminal, std::set<Nonterminal> > trules_t;

    cfg_tree_map_t(const rules_t& rules)
      : rules_(rules) {
      // Construct in
      const std::set<Nonterminal>& nt_set = rules_.nonterminals();

      // Construct initial trace.
      earley_trace_t<Nonterminal> initial(nt_set.begin(), nt_set.end());

      typedef typename std::set<Nonterminal>::const_iterator iter;
      for (iter i = nt_set.begin(); i != nt_set.end(); ++i) {
        cfg_tree_t<Terminal, Nonterminal> tree(rules_, trules_, *i, initial);
        map_.insert(std::make_pair(*i, tree));
      }
    }

    /** Add terminal to map. */
    template<typename NonterminalIterator>
    void add_terminal(const Terminal& terminal,
                      NonterminalIterator nt_begin,
                      NonterminalIterator nt_end) {
      terminals_.insert(terminal);
      trules_[terminal] = std::set<Nonterminal>(nt_begin, nt_end);
    }

    /** Return Chomsky rules for cfg. */
    const rules_t& rules(void) const {
      return rules_;
    }

    /** Return terminals added so far. */
    const std::set<Terminal>& terminals(void) const {
      return terminals_;
    }

    /** Return the nonterminals that the given terminal generates. */
    const std::set<Nonterminal>& generators(const Terminal& t) const {
      return trules_.find(t)->second;
    }

    /** Return cfg tree for nonterminal. */
    cfg_tree_t<Terminal, Nonterminal>& operator[](const Nonterminal& nt) {
      return map_.find(nt)->second;
    }

    /** Return cfg tree for nonterminal. */
    const cfg_tree_t<Terminal, Nonterminal>&
        operator[](const Nonterminal& nt) const {
      return map_.find(nt)->second;
    }
  private:
    rules_t rules_;
    /** Set of terminal symbols added so far. */
    std::set<Terminal> terminals_;
    trules_t trules_;
    std::map<Nonterminal, cfg_tree_t<Terminal, Nonterminal> > map_;
  };


  /** Stores information about a split that is need in a classifier. */
  template<typename Terminal, typename Nonterminal>
  struct dfa_split_t {
    typedef earley_trace_t<Nonterminal> trace_t;

    /** Constructs a new split. */
    dfa_split_t(const Nonterminal& nt_arg,
                size_t node_arg,
                const cons_list_t<Terminal>& d_arg,
                bool existing_accept_arg,
                const std::vector<Terminal>& path_arg,
                const trace_t& trace_arg)
      : nonterminal(nt_arg),
        node(node_arg),
        distinguisher(d_arg),
        existing_accept(existing_accept_arg),
        path(path_arg),
        trace(trace_arg) {
    }
    /** Nonterminal whose classifier should be split. */
    Nonterminal nonterminal;
    /** Leaf node that should be split. */
    size_t node;
    /** Distinguisher to split on. */
    cons_list_t<Terminal> distinguisher;
    /** True if the existing leaf should accept. */
    bool existing_accept;
    /** Path trace ran along. */
    std::vector<Terminal> path;
    /** Trace to label new leaf with. */
    trace_t trace;
  };

  /** Writes information about split to stream. */
  template<typename Terminal, typename Nonterminal>
  std::ostream& operator<<(std::ostream& o,
                           const dfa_split_t<Terminal, Nonterminal>& split) {
    o << "nt: " << split.nonterminal
      << " node: " << split.node
      << " accept: " << split.existing_accept;
    return o;
  }


  template<typename Terminal, typename Nonterminal>
  class cfg_subset_t {
  public:
    /** Type of trace for this cfg_subset. */
    typedef earley_trace_t<Nonterminal> trace_t;
    /** Type of map for primary nodes. */
    typedef std::map<Nonterminal, size_t> primary_t;

    /** Constructs an initial subset with the given nonterminals. */
    template<typename NonterminalIterator>
    cfg_subset_t(NonterminalIterator nt_begin, NonterminalIterator nt_end)
      : trace_(nt_begin, nt_end) {
      // Define initial primary states.
      for (NonterminalIterator i = nt_begin; i != nt_end; ++i)
        primary_.insert(std::make_pair(*i, 0));
      // As primary states are guaranteed to not be accepting, secondary
      // states is guaranteed to be empty.
    }

    /** Returns path of terminals followed to this subset. */
    const std::vector<Terminal>& path(void) const {
      return path_;
    }

    /** Returns nonterminals accepted by path. */
    const std::set<Nonterminal>& accepted(void) const {
      return accepted_;
    }

    /** Returns Earley trace built along path. */
    const trace_t& trace(void) const {
      return trace_;
    }

    /** Returns primary nodes. */
    const primary_t& primary(void) const {
      return primary_;
    }

    typedef cfg_tree_t<Terminal, Nonterminal> tree_t;

    /**
     * Updates this subset to notify it that the node in the given tree
     * has been split into a branch.
     */
    void recompute(const tree_t& tree, size_t node) {
      // Recompute primary node.
      const Nonterminal& nt = tree.nonterminal();
      typedef typename primary_t::iterator pri_iter;
      pri_iter ip = primary_.find(nt);
      if (ip == primary_.end())
        throw std::logic_error("Could not find expected primary.");
      if (ip->second == node) {
        // Get appropriate child of leaf
        // Note that we set empty_accepts to false since the only way it
        // matters if node is the root, and in that case we know the trace_
        // rejects.
        ip->second = tree.pick_child(node, trace_, false);
      }

      // Recompute secondary nodes if any.
      // Find iterator pointing to node if there is one.
      typedef typename followup_map_t::iterator follow_iter;
      follow_iter iold = followups_.find(node_t(nt, node));
      if (iold != followups_.end()) {
        // Get old indices.
        const std::set<size_t>& indices = iold->second;
        // Iterate through indices to split on each.
        typedef std::set<size_t>::const_iterator start_iter;
        for (start_iter i = indices.begin(); i != indices.end(); ++i) {
          size_t cur_start = *i;
          trace_t suffix = trace_.suffix(cur_start);
          size_t new_node = tree.pick_child(node, suffix, false);
          followups_[node_t(nt, new_node)].insert(cur_start);
        }
        // Erase iold from secondary since it points to old node.
        followups_.erase(iold);
      }
    }

    /** Returns the eq subset for the subset and nonterminal. */
    const eq_subset_t<Nonterminal> eq_subset(void) const {
      eq_subset_t<Nonterminal> result;
      // Add primary nodes.
      typedef typename primary_t::const_iterator pri_iter;
      for (pri_iter i = primary_.begin(); i != primary_.end(); ++i)
        result.add_primary(*i);
      // Add followup nodes.
      typedef typename followup_map_t::const_iterator follow_iter;
      for (follow_iter i = followups_.begin(); i != followups_.end(); ++i)
        result.add_secondary(i->first);
      return result;
    }

    /** Identifies a specific node in the classifier for some nonterminal. */
    typedef std::pair<Nonterminal, size_t> node_t;

    /** Returns the set of all nodes referenced in this subset. */
    const std::set<node_t> nodes(void) const {
      std::set<node_t> result;
      // Add primary nodes.
      typedef typename primary_t::const_iterator pri_iter;
      for (pri_iter i = primary_.begin(); i != primary_.end(); ++i)
        result.insert(*i);
      // Add secondary nodes.
      typedef typename followup_map_t::const_iterator follow_iter;
      for (follow_iter i = followups_.begin(); i != followups_.end(); ++i)
        result.insert(i->first);
      return result;
    }

    typedef dfa_split_t<Terminal, Nonterminal> split_t;

    /**
     * Attempts to construct a new subset by exploring this subset with a
     * terminal.  This will either return the new subset or identify a tree
     * node that should be split.
     */
    boost::variant<cfg_subset_t<Terminal, Nonterminal>, split_t>
    explore(const cfg_tree_map_t<Terminal, Nonterminal>& map,
            const Terminal& terminal) const {
      // Construct a new subset.
      cfg_subset_t<Terminal, Nonterminal> result(trace_);

      // Parse terminal with result's trace.
      typedef std::set< std::pair<size_t, Nonterminal> > generated_set_t;
      const std::set<Nonterminal>& found = map.generators(terminal);
      // Set of recognitions.
      generated_set_t gen =
              parse(map.rules(), result.trace_, found.begin(), found.end());

      typedef boost::optional<split_t> opt_split_t;

      // For each primary node
      typedef typename primary_t::const_iterator pri_iter;
      for (pri_iter i = primary_.begin(); i != primary_.end(); ++i) {
        const Nonterminal& nt = i->first;
        size_t prev_node = i->second;
        const cfg_tree_t<Terminal, Nonterminal>& tree = map[nt];
        size_t cur_node = tree.next_node(prev_node, terminal);

        bool trace_accept = gen.count(std::make_pair(0, nt)) > 0;
        opt_split_t split =
                check_next_node(tree, path_, prev_node, terminal,
                                cur_node, result.trace_, trace_accept);
        // Return split if we foudn one.
        if (split) return *split;
        // Add next primary mode to new subset.
        result.primary_.insert(node_t(nt, cur_node));
        // If trace accepted nt.
        if (trace_accept) {
          // Add nonterminals to result.accepted_
          result.accepted_.insert(nt);
          // Number of terminals read after this one.
          size_t path_length = path_.size() + 1;
          // Add initial nodes to result.followups_
          const std::set<Nonterminal>& follow = tree.followups();
          typedef typename  std::set<Nonterminal>::const_iterator set_iter;
          for (set_iter i = follow.begin(); i != follow.end(); ++i) {
            node_t initial_node(*i, map[*i].initial());
            result.followups_[initial_node].insert(path_length);
          }
        }
      }

      // Iterate through followups.
      typedef typename followup_map_t::const_iterator follow_iter;
      for (follow_iter i = followups_.begin(); i != followups_.end(); ++i) {
        const Nonterminal& nt = i->first.first;
        size_t prev_node = i->first.second;
        const std::set<size_t>& start_indices = i->second;
        const cfg_tree_t<Terminal, Nonterminal>& tree = map[nt];
        size_t cur_node = tree.next_node(prev_node, terminal);

        // Check all suffixes with the given start indices.
        opt_split_t split =
                check_suffixes(tree, path_, prev_node, terminal, cur_node,
                               result.trace_, gen, start_indices);
        // Return split if we find one.
        if (split) return *split;
        // Add cur_node and start indices to followups.
        result.followups_[node_t(nt, cur_node)].insert(
                start_indices.begin(), start_indices.end());
      }

      // Initialize result's path
      result.path_.reserve(path_.size() + 1);
      result.path_.insert(result.path_.end(), path_.begin(), path_.end());
      result.path_.push_back(terminal);

      return result;
    }

  private:
    /**
     * Returns the node associated to the trace in the given tree or returns
     * a split if the tree should be split.
     *
     * @param tree Decision tree
     * @param prev_node Index of node in tree.
     * @param terminal Terminal to read next.
     * @param trace Earley trace after reading terminal
     * @param gen Generated set for terminal.
     */
    static
    boost::optional<split_t>
    check_next_node(const cfg_tree_t<Terminal, Nonterminal>& tree,
                    const std::vector<Terminal>& prev_path,
                    size_t prev_node,
                    const Terminal& terminal,
                    size_t cur_node,
                    const earley_trace_t<Nonterminal>& trace,
                    bool trace_accepts) {
      const Nonterminal& nt = tree.nonterminal();
      // If tree for nonterminal has a single leaf.
      if ((tree.size() == 1) && trace_accepts)
        throw std::logic_error(
                  "Accepting node for single leaf tree detected.");
      size_t trace_node = tree.find_node(trace, trace_accepts);
      // If current rep and trace rep are different
      if (trace_node != cur_node) {
        // Get branch that distinguishes cur_node and trace_node
        // and whether cur_node is on accepting side.
        std::pair<size_t, bool> sep_pair
                = tree.separator(cur_node, trace_node);
        // Create distinguisher
        cons_list_t<Terminal> d(terminal,
                                tree.distinguisher(sep_pair.first));
        earley_trace_t<Nonterminal> prev_trace = trace;
        prev_trace.pop_back();
        // Construct split and return it.
        return split_t(nt, prev_node, d, sep_pair.second,
                       prev_path, prev_trace);
      }
      return boost::none;
    }

    /**
     * Checks that the tree node for each suffix of the trace with the given
     * suffix equals cur_node.
     */
    static
    boost::optional<split_t>
    check_suffixes(const cfg_tree_t<Terminal, Nonterminal>& tree,
                   const std::vector<Terminal>& prev_path,
                   size_t prev_node,
                   const Terminal& terminal,
                   size_t cur_node,
                   const trace_t& trace,
                   const std::set< std::pair<size_t, Nonterminal> >& gen,
                   const std::set<size_t>& start_indices) {
      const Nonterminal& nt = tree.nonterminal();
      // For each start index.
      typedef std::set<size_t>::const_iterator iter;
      for (iter i = start_indices.begin(); i != start_indices.end(); ++i) {
        size_t cur_start = *i;
        // Get suffix of trace.
        std::vector<Terminal> suffix_path(prev_path.begin() + cur_start,
                                          prev_path.end());
        earley_trace_t<Nonterminal> suffix_trace = trace.suffix(cur_start);
        // Determine if trace recognized nonterminal at start index.
        bool suffix_accepts = gen.count(std::make_pair(cur_start, nt)) > 0;
        // Check suffix
        typedef boost::optional<split_t> opt_split_t;
        opt_split_t result =
          check_next_node(tree, suffix_path, prev_node, terminal,
                          cur_node, suffix_trace, suffix_accepts);
        if (result) return result;
      }
      return boost::none;
    }

    /** Constructs a subset with the given trace. */
    cfg_subset_t(const trace_t& trace)
      : trace_(trace) {
    }

    /**
     * Maps secondary dfa nodes to the set of starting index of substrings
     * they may recognize.
     */
    typedef std::map<node_t, std::set<size_t> > followup_map_t;


    /** Path of terminal symbols that lead to this subset. */
    std::vector<Terminal> path_;
    /** Set of nonterminals accepted from start. */
    std::set<Nonterminal> accepted_;
    /** Earley trace leading up to this subset. */
    trace_t trace_;
    /** Primary states for this subset. */
    primary_t primary_;
    /** Secondary states for this subset. */
    followup_map_t followups_;
  };

  /** Writes aspects of subset to stream. */
  template<typename Terminal, typename Nonterminal>
  std::ostream& operator<<(std::ostream& o,
                           const cfg_subset_t<Terminal, Nonterminal>& s) {
    typedef cfg_subset_t<Terminal, Nonterminal> subset_t;
    o << "path: \""
      << make_range_writer(s.path().begin(), s.path().end(), "")
      << "\" primary: {";
    typedef typename subset_t::primary_t::const_iterator primary_iter;
    for (primary_iter i = s.primary().begin(); i != s.primary().end(); ++i) {
      if (i != s.primary().begin())
        o << ", ";

      o << "(" << i->first << ", " << i->second << ")";
    }
    o << "}";
    return o;
  }

  template<typename Terminal, typename Nonterminal>
  class instance_map_t {
  public:
    template<typename RuleIterator>
    instance_map_t(RuleIterator rules_begin, RuleIterator rules_end) {
      for (RuleIterator i = rules_begin; i != rules_end; ++i) {
        const cfg_rule_t<Nonterminal>& cur_rule = *i;
        // See if rule's lhs is in either argument.
        bool cyclic = (cur_rule.lhs == cur_rule.first)
                   || (cur_rule.lhs == cur_rule.second);
        if (!cyclic) {
          // Add implication for each nonterminal on rhs.
          implications_[cur_rule.first].insert(cur_rule);
          implications_[cur_rule.second].insert(cur_rule);
        }
      }
    }

    template<typename NonterminalIterator>
    void add_terminal(const Terminal& terminal,
                      NonterminalIterator nt_begin,
                      NonterminalIterator nt_end) {
      // Set that contains nonteminals we need to check for a shorter string.
      std::set<Nonterminal> smaller_nonterminals;
      // Initialize new with terminal.
      for (NonterminalIterator i = nt_begin; i != nt_end; ++i) {
        // Find iterator for current nonterminal in instance map.
        instance_iter cur_instance = instances_.find(*i);
        // If there nonterminal is not bound.
        if (cur_instance == instances_.end()) {
          // Add new instance with terminal and update smaller nonterminals.
          add_new_instance(*i, instance_t(1, terminal));
          smaller_nonterminals.insert(*i);
        // Else if nonterminal is bound to a vector with size > 1
        } else if (cur_instance->second.size() > 1) {
          // Replace vector with terminal and add to smaller.
          cur_instance->second = instance_t(1, terminal);
          smaller_nonterminals.insert(*i);
        }
      }
      // While there are smaller_nonterminals to process.
      while (!smaller_nonterminals.empty()) {
        // Pop first smaller nonterminal from set.
        Nonterminal cur_nt = *smaller_nonterminals.begin();
        smaller_nonterminals.erase(smaller_nonterminals.begin());

        const std::set<rule_t>& cur_rules = rules(cur_nt);

        // For each rule for nonterminal.
        typedef typename std::set<rule_t>::const_iterator iter;
        for (iter i = cur_rules.begin(); i != cur_rules.end(); ++i) {
          instance_iter first_iter = instances_.find(i->first);
          instance_iter second_iter = instances_.find(i->second);
          // If both first and second iterator are bound.
          if (( first_iter != instances_.end())
           && (second_iter != instances_.end())) {
            // Get instance vectors for first and second.
            const instance_t& first = first_iter->second;
            const instance_t& second = second_iter->second;

            // Find iterator for lhs in instances.
            instance_iter lhs_iter = instances_.find(i->lhs);
            // If lhs is not bound.
            if (lhs_iter == instances_.end()) {
              // Add new instance for lhs.
              add_new_instance(i->lhs, make_instance(first, second));
              smaller_nonterminals.insert(i->lhs);
            } else if (lhs_iter->second.size()
                    > first.size() + second.size()) {
              // Replace vector with terminace and add to smaller.
              lhs_iter->second = make_instance(first, second);
              smaller_nonterminals.insert(i->lhs);
            }
          }
        }
      }
    }

    bool has_next(void) const {
      return !queue_.empty();
    }

    const Nonterminal& next_nonterminal(void) const {
      return queue_.front()->first;
    }

    const std::vector<Terminal>& next_instance(void) const {
      return queue_.front()->second;
    }

    void pop_next(void) {
      queue_.pop_front();
    }
  private:
    typedef std::vector<Terminal> instance_t;
    /** Map from nonterminals to a vector of terminals that reaches it. */
    typedef std::map<Nonterminal, instance_t> instances_t;
    typedef typename instances_t::iterator instance_iter;
    typedef cfg_rule_t<Nonterminal> rule_t;
    /** Map from nonterminals to rules that contain nonterminal. */
    typedef std::map<Nonterminal, std::set<rule_t> > implication_map_t;

    /** Constructs instance by concatenating first and second. */
    const instance_t make_instance(const instance_t& first,
                                   const instance_t& second) {
      instance_t result = first;
      result.insert(result.end(), second.begin(), second.end());
      return result;
    }

    /** Adds new entry to instances and appends to queue. */
    instance_iter
    add_new_instance(const Nonterminal& nt, const instance_t& t) {
      instance_iter result = instances_.insert(std::make_pair(nt, t)).first;
      queue_.push_back(result);
      return result;
    }

    /** Returns rules associated as implications of rhs. */
    const std::set<rule_t>& rules(const Nonterminal& rhs) const {
      typedef typename implication_map_t::const_iterator iter;
      iter i = implications_.find(rhs);
      if (i != implications_.end()) {
        return i->second;
      } else {
        static std::set<rule_t> empty_set;
        return empty_set;
      }
    }

    instances_t instances_;
    std::deque<instance_iter> queue_;
    implication_map_t implications_;
  };

  /**
   * Queue that manages directions to explore.  In addition, to allowing
   * one to add all explorations for a terminal or subset, this queue tracks
   * which subset explorations lead to, and allows clients to add all
   * explorations that lead to a subset back to queue.
   */
  template<typename Terminal>
  class cfg_explore_queue_t {
  public:
    /** A pair containing a subset to explore from and terminal to use. */
    typedef std::pair<size_t, Terminal> pair_t;

    /** Construct queue with the given number of initial subsets. */
    explicit cfg_explore_queue_t(size_t initial_subset_count)
      : backlinks_(initial_subset_count) {
    }

    void add_terminal(const Terminal& terminal) {
      // Append to terminals
      terminals_.push_back(terminal);
      // Add every subset with this terminal to pending.
      for (size_t i = 0; i != backlinks_.size(); ++i)
        pending_.insert(pair_t(i, terminal));
    }

    /** Explore subset with all terminals. */
    void explore_subset(size_t subset) {
      typedef typename std::vector<Terminal>::const_iterator iter;
      for (iter i = terminals_.begin(); i != terminals_.end(); ++i) {
        pair_t cur_pair(subset, *i);
        // Add to pending.
        pending_.insert(cur_pair);
        // Erase information of previous exploration.
        typedef typename explorations_t::iterator explore_iter;
        explore_iter iexplore = explorations_.find(cur_pair);
        if (iexplore != explorations_.end()) {
          backlinks_[iexplore->second].erase(cur_pair);
          explorations_.erase(iexplore);
        }
      }
    }

    /** Adds all exploration paths that reached subset to pending. */
    void explore_backlinks(size_t subset) {
      std::set<pair_t>& prev_pairs = backlinks_[subset];
      typedef typename std::set<pair_t>::const_iterator iter;
      for (iter i = prev_pairs.begin(); i != prev_pairs.end(); ++i) {
        pending_.insert(*i);
        explorations_.erase(*i);
      }
      prev_pairs.clear();
    }

    /** Return true if there is an exploration pending. */
    bool has_next(void) const {
      return !pending_.empty();
    }

    /** Return next subset we should explore from. */
    size_t next_subset(void) const {
      return pending_.begin()->first;
    }

    /** Return next terminal that should be used in exploring. */
    const Terminal& next_terminal(void) const {
      return pending_.begin()->second;
    }

    /**
     * Mark that the next exploration has been explored and found to
     * reach the given subset.  If this is a new subset, it will be added
     * automatically.
     */
    void set_next_explored(size_t destination_subset) {
      typedef typename std::set<pair_t>::iterator pending_iter;
      pending_iter next_pending = pending_.begin();

      // Increment number of subsets to accomadate destination_subset.
      while (destination_subset >= backlinks_.size()) {
        // Get index of next subset.
        size_t index = backlinks_.size();
        // Add new entry to backlinks.
        std::set<pair_t> empty_set;
        backlinks_.push_back(empty_set);
        // Add every terminal from index to pending.
        typedef typename std::vector<Terminal>::const_iterator iter;
        for (iter i = terminals_.begin(); i != terminals_.end(); ++i)
          pending_.insert(pair_t(index, *i));
      }

      // Update exploration, backlinks, and erase next_pending.
      explorations_[*next_pending] = destination_subset;
      backlinks_[destination_subset].insert(*next_pending);
      pending_.erase(next_pending);
    }
  private:
    /** Map used to store previous exploration paths */
    typedef std::map<pair_t, size_t> explorations_t;
    /** Terminal symbols added to explore. */
    std::vector<Terminal> terminals_;
    /** Map of previous explorations. */
    explorations_t explorations_;
    /**
     * Vector that maps each subset to pairs that lead to it.
     * The size of the vector is equivalent to the total number of subsets.
     */
    std::vector< std::set<pair_t> > backlinks_;
    /** Set of pending explorations. */
    std::set<pair_t> pending_;
  };

  /**
   * This class searches a context free grammar to compute all of the
   * subsets of the nonterminals that generate a common string.  It is
   * conjectured that if a subset of terminals generate a common string, the
   * explorer will eventually return that subset.  However, this process
   * will only terminate if the language generated by each nonterminal is
   * regular.  The explorer is partially incremental in that new terminal
   * symbols may be introduced as the search continues.
   */
  template<typename Terminal, typename Nonterminal>
  class cfg_explorer_t {
  public:
    typedef chomsky_rules_t<Nonterminal> rules_t;
    typedef earley_trace_t<Nonterminal> trace_t;
    typedef cfg_subset_t<Terminal, Nonterminal> subset_t;

    /** Construct new explorer. */
    template<typename NonterminalIterator,
             typename RuleIterator>
    cfg_explorer_t(NonterminalIterator nt_begin,
                   NonterminalIterator nt_end,
                   RuleIterator rules_begin,
                   RuleIterator rules_end)
      : tree_map_(rules_t(nt_begin, nt_end, rules_begin, rules_end)),
        instances_(rules_begin, rules_end),
        queue_(1),
        next_reachable_(reachables_.end()) {
//      cerr << "Nonterminals {"
//           << make_range_writer(nt_begin, nt_end, ", ")
//           << "}" << endl;
//      cerr << "Rules:" << endl
//           << make_range_writer(rules_begin, rules_end, "\n")
//           << endl;
      // Add initial subset.
      const std::set<Nonterminal>& nt_set = tree_map_.rules().nonterminals();
      add_subset(subset_t(nt_set.begin(), nt_set.end()));
    }


    template<typename NonterminalIterator>
    void add_terminal(const Terminal& terminal,
                      NonterminalIterator nt_begin,
                      NonterminalIterator nt_end) {
      //TODO: Check that all nonterminals have already been registered.
//      cerr << "Adding terminal " << terminal << " ::=";
//      for (NonterminalIterator i = nt_begin; i != nt_end; ++i)
//        cerr << " " << *i;
//      cerr << endl;
      instances_.add_terminal(terminal, nt_begin, nt_end);
      tree_map_.add_terminal(terminal, nt_begin, nt_end);
      // Add each new exploration to pendings.
      queue_.add_terminal(terminal);
      // While nonterminals are first noticed to be nont
      while (instances_.has_next()) {
        const Nonterminal& cur_nt = instances_.next_nonterminal();
        const std::vector<Terminal>& cur_path = instances_.next_instance();

        // Build trace for path
        const std::set<Nonterminal>& searches
                = tree_map_.rules().searches(cur_nt);
        trace_t trace(searches.begin(), searches.end());
        typedef typename std::vector<Terminal>::const_iterator iter;
        for (iter i = cur_path.begin(); i != cur_path.end(); ++i) {
          const std::set<Nonterminal>& nt_set = tree_map_.generators(*i);
          parse(tree_map_.rules(), trace, nt_set.begin(), nt_set.end());
        }
        typedef cfg_tree_t<Terminal, Nonterminal> tree_t;
        // Split decision tree for nonterminal
        tree_t& cur_tree = tree_map_[cur_nt];
        cons_list_t<Terminal> empty_d;
        cur_tree.make_branch(0, empty_d, false, cur_path, trace);
        recompute_after_split(cur_nt, 0);
        instances_.pop_next();
      }
//      cerr << "Stop Adding terminal" << endl;
    }

    /**
     * Performs some finite amount of computation to explore for additional
     * states.
     */
    void work(void) {
      if (has_reachable() || complete())
        return;
      // Perform checked explore
      typedef dfa_split_t<Terminal, Nonterminal> split_t;
      typedef boost::variant<subset_t, split_t> variant_t;
      const subset_t& cur_subset = subsets_[queue_.next_subset()];

      variant_t var = cur_subset.explore(tree_map_, queue_.next_terminal());

      // If exploration induces split
      if (split_t* cur_split = boost::get<split_t>(&var)) {
        const Nonterminal& cur_nt = cur_split->nonterminal;
        // Perform split on tree.
        tree_t& cur_tree = tree_map_[cur_nt];
        cur_tree.make_branch(cur_split->node,
                             cur_split->distinguisher,
                             cur_split->existing_accept,
                             cur_split->path,
                             cur_split->trace);
//        cerr << "Induced split" << cur_split->node << endl;
//        cerr << cur_tree;
        recompute_after_split(cur_nt, cur_split->node);
      } else { // Exploration yielded new subset.
        const subset_t& new_subset = boost::get<subset_t>(var);
        std::pair<size_t, bool> add_result = add_subset(new_subset);
        queue_.set_next_explored(add_result.first);
      }
    }

    /**
     * Returns true if explorer knows that all reachable subsets have been
     * returned.
     */
    bool complete(void) const {
      return !queue_.has_next();
    }

    /** Returns true if the explorer has found a new subset. */
    bool has_reachable(void) const {
      return next_reachable_ != reachables_.end();
    }

    /**
     * Returns subset of reachable states that generate a common string.
     * that no nonterminal outside of subset generates.
     */
    const std::set<Nonterminal>& reachable(void) const {
      return next_reachable_->first;
    }

    /** Returns an example of a string that generates subset. */
    const std::vector<Terminal>& string(void) const {
      return next_reachable_->second;
    }

    /** Mark the most recent subset as reported. */
    void pop_reachable(void) {
      next_reachable_ = reachables_.end();
    }
  private:
    typedef std::pair<Nonterminal, size_t> node_t;
    typedef cfg_tree_t<Terminal, Nonterminal> tree_t;

    /** Update node_subset_map_ to add subset_index to each node entry. */
    void expand_node_subset_map(const std::set<node_t>& nodes,
                                size_t subset_index) {
      // Iterate through nodes and add subset_index to each entry in map.
      typedef typename std::set<node_t>::const_iterator iter;
      for (iter i = nodes.begin(); i != nodes.end(); ++i)
        node_subset_map_[*i].insert(subset_index);
    }

    /**
     * Update previously computed subsets to reflect that a node
     * in the tree for the given nonterminal has split.
     */
    void recompute_after_split(const Nonterminal& nt, size_t node) {
      tree_t& tree = tree_map_[nt];
      // For each subset that contains split node.
      node_t old_node(nt, node);
      const std::set<size_t>& subsets = node_subset_map_[old_node];
      typedef std::set<size_t>::const_iterator subset_iter;
      for (subset_iter i = subsets.begin(); i != subsets.end(); ++i) {
        size_t cur_index = *i;
        subset_t& cur_subset = subsets_[cur_index];
        // Erase current subset from map.
        eq_subset_t<Nonterminal> cur_eq_subset = cur_subset.eq_subset();
        eq_subset_map_.erase(cur_eq_subset);
        // Recompute states for subset.
        cur_subset.recompute(tree, node);
        // Add new subset to map.
        eq_subset_t<Nonterminal> new_eq_subset = cur_subset.eq_subset();
        eq_subset_map_.insert(std::make_pair(new_eq_subset, cur_index));
        // Add new node to node_subset_map_
        expand_node_subset_map(cur_subset.nodes(), cur_index);
        // Add all exploration from and to current state.
        queue_.explore_backlinks(*i);
        queue_.explore_subset(*i);
      }
      // Erase old node from set.
      node_subset_map_.erase(old_node);
    }

    /** Check subset to see if set of accepted states is new. */
    void consider_new_reachable(const subset_t& subset) {
      // The subset trace must have length at least 2 to be considered.
      const static size_t min_length = 2;
      if (subset.path().size() < min_length)
        return;

      // Get set of nonterminals accepted by new_subset
      const std::set<Nonterminal>& accepted = subset.accepted();
      reachable_iter i = reachables_.find(accepted);
      // If new accepted state.
      if (i == reachables_.end()) {
        const std::vector<Terminal>& path = subset.path();
        next_reachable_ =
                reachables_.insert(std::make_pair(accepted, path)).first;
      }
    }

    /**
     * Adds subset to explorer if it the eq_subset is new.
     * @param subset Subet to add.
     * @return Pair indicating index of subset and whether it was new.
     */
    std::pair<size_t, bool> add_subset(const subset_t& subset) {
      eq_subset_t<Nonterminal> eq_subset = subset.eq_subset();
      // Check if node subset of cfg_subet is new.
      typedef typename eq_subset_map_t::const_iterator eq_iter;
      eq_iter i = eq_subset_map_.find(eq_subset);
      if (i == eq_subset_map_.end()) {
        // Get index of new subset.
        size_t index = subsets_.size();
        // Add subset to subsets_
        subsets_.push_back(subset);
        // Add node subset to eq_subset_map
        eq_subset_map_.insert(std::make_pair(eq_subset, index));
        // Add new subset to node_subset_map_.
        expand_node_subset_map(subset.nodes(), index);
        // See if this this should be added to reachables.
        consider_new_reachable(subset);
        return std::make_pair(index, true);
      } else {
        return std::make_pair(i->second, false);
      }
    }

    typedef std::map<std::set<Nonterminal>, std::vector<Terminal> >
            reachable_map_t;
    typedef typename reachable_map_t::const_iterator reachable_iter;

    /** A pair identifying a starting subset and a terminal to explore in. */
    typedef std::pair<size_t, Terminal> explore_t;

    /** Map from eq_subsets to indices. */
    typedef std::map<eq_subset_t<Nonterminal>, size_t> eq_subset_map_t;

    typedef std::map<node_t, std::set<size_t> > node_subset_map_t;

    /** Decision trees for nonterminals. */
    cfg_tree_map_t<Terminal, Nonterminal> tree_map_;

    /** Tracks when language for nonterminals are known to be nonempty. */
    instance_map_t<Terminal, Nonterminal> instances_;

    // Invariants:
    // If an explore_t is in pendings_, it does not in any backlinks set.

    /** Subsets explored so far. */
    std::vector<subset_t> subsets_;
    /** Maps eq_subsets to index of cfg_subset creating it. */
    eq_subset_map_t eq_subset_map_;
    /** Maps each node the the indices of the subsets that contain it. */
    node_subset_map_t node_subset_map_;
    typedef cfg_explore_queue_t<Terminal> explore_queue_t;
    /** Pending explorations. */
    explore_queue_t queue_;

    /**
     * Maps reachable sets of nonterminals to a vector that is generated
     * by them.
     */
    reachable_map_t reachables_;
    /** Next set of reachable states that should be returned. */
    reachable_iter next_reachable_;
  };
}}

#endif
