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
#ifndef _earley_hh_
#define _earley_hh_

#include <map>
#include <set>
#include <stdexcept>
#include <vector>
#include <boost/shared_ptr.hpp>

#include "qcontainer.hh"
#include "trans_closure.hh"

//TODO: Cite Practical Earley parsing paper to explain scanning, predictor,
// and completer terminology.

namespace ceta {
namespace cfg {
  /** A context free rule lhs ::= first second. */
  template<typename Nonterminal>
  struct cfg_rule_t {
    /** Construct a context free rule with the given nonterminals. */
    cfg_rule_t(const Nonterminal& lhs_arg,
               const Nonterminal& first_arg,
               const Nonterminal& second_arg)
      : lhs(lhs_arg),
        first(first_arg),
        second(second_arg) {
    }
    /** Nonterminal on left-hand-side of rule. */
    Nonterminal lhs;
    /** First nonterminal on right-hand-side of rule. */
    Nonterminal first;
    /** Second nonterminal on right-hand-side of rule. */
    Nonterminal second;
  };
  /** Compare's rule's based on ordering of nonterminal components. */
  template<typename Nonterminal>
  bool operator<(const cfg_rule_t<Nonterminal>& x,
                 const cfg_rule_t<Nonterminal>& y) {
    return (x.lhs  < y.lhs)
        || (x.lhs == y.lhs) && (x.first  < y.first)
        || (x.lhs == y.lhs) && (x.first == y.first) && (x.second < y.second);
  }
  /** Write rule to ostream. */
  template<typename Nonterminal>
  std::ostream& operator<<(std::ostream& o,
                           const cfg_rule_t<Nonterminal>& rule) {
    o << rule.lhs << " ::= " << rule.first << " " << rule.second;
    return o;
  }

  /** A context free rule lhs ::= rhs. */
  template<typename Nonterminal>
  struct cfg_erule_t {
    /** Construct a context free rule with the given nonterminals. */
    cfg_erule_t(const Nonterminal& lhs_arg,
                const Nonterminal& rhs_arg)
      : lhs(lhs_arg),
        rhs(rhs_arg) {
    }
    /** Nonterminal on left-hand-side of rule. */
    Nonterminal lhs;
    /** Nonterminal on right-hand-side of rule. */
    Nonterminal rhs;
  };
  /** Compare's rule's based on ordering of nonterminal components. */
  template<typename Nonterminal>
  bool operator<(const cfg_erule_t<Nonterminal>& x,
                 const cfg_erule_t<Nonterminal>& y) {
    return (x.lhs  < y.lhs)
        || (x.lhs == y.lhs) && (x.rhs  < y.rhs);
  }
  /** Write rule to ostream. */
  template<typename Nonterminal>
  std::ostream& operator<<(std::ostream& o,
                           const cfg_erule_t<Nonterminal>& rule) {
    return o << rule.lhs << " ::= " << rule.rhs;
  }

  template<typename Nonterminal>
  class chomsky_rules_t {
    typedef std::vector<cfg_rule_t<Nonterminal> > rule_vector_t;
  public:
    /** Construct empty set of chomsky rules. */
    chomsky_rules_t(void) {
    }

    /** Construct chomsky rules with given nonterminals and rules. */
    template<typename NonterminalIterator,
             typename RuleIterator,
             typename ERuleIterator>
    chomsky_rules_t(NonterminalIterator nt_begin,
                    NonterminalIterator nt_end,
                    RuleIterator rules_begin,
                    RuleIterator rules_end,
                    ERuleIterator erules_begin,
                    ERuleIterator erules_end) {
      for (NonterminalIterator i = nt_begin; i != nt_end; ++i)
        add_nonterminal(*i);
      for (RuleIterator i = rules_begin; i != rules_end; ++i)
        add_rule(i->lhs, i->first, i->second);
      for (ERuleIterator i = erules_begin; i != erules_end; ++i)
        add_erule(i->lhs, i->rhs);
    }

    /** Adds new nonterminal symbol to parser. */
    bool add_nonterminal(const Nonterminal& nt) {
      bool added = nonterminals_.insert(nt).second;
      if (added)
        search_map_.insert(make_pair(nt, nt_set_t(&nt, &nt + 1)));
      return added;
    }

    /** Adds a rule from a nonterminal to two nonterminals. */
    void add_rule(const Nonterminal& lhs,
                  const Nonterminal& first_arg,
                  const Nonterminal& second_arg) {
      rules_.push_back(cfg_rule_t<Nonterminal>(lhs, first_arg, second_arg));
      search_map_[lhs].insert(first_arg);
      followup_map_[first_arg][lhs].insert(second_arg);
    }

    /** Adds an epsilon rule lhs := rhs */
    void add_erule(const Nonterminal& lhs, const Nonterminal& rhs) {
      search_map_[lhs].insert(rhs);
      enext_[rhs].insert(lhs);
    }

    /** Returns set of nonterminals. */
    const std::set<Nonterminal>& nonterminals(void) const {
      return nonterminals_;
    }

    /** Returns rules added so far. */
    const rule_vector_t& rules(void) const {
      return rules_;
    }

    /**
     * Returns set containing a nonterminal lhs if "lhs := rhs" is a rule.
     */
    const std::set<Nonterminal>& enext(const Nonterminal& rhs) const {
      typename nt_set_map_t::const_iterator i = enext_.find(rhs);
      static const nt_set_t empty_set;
      return (i != enext_.end()) ? i->second : empty_set;
    }

    /**
     * Adds all nonterminals we should start searching for to set when we
     * start searching for nt.
     */
    void add_and_close_searches(std::set<Nonterminal>& set,
                                const Nonterminal& nt) const {
      add_and_close(search_map_, set, nt);
    }

    /** Set of nonterminals. */
    typedef std::set<Nonterminal> nt_set_t;

    /** Map from nonterminals to set of nonterminals. */
    typedef std::map<Nonterminal, nt_set_t> nt_set_map_t;

    /**
     * Returns a map that pairs nonterminals that appear on the
     * left-hand-side of a rule with the nonterminals that appear
     * as the second argument on the right-hand-side of a rule whose first
     * argument is the given nonterminal.
     */
    const nt_set_map_t& followups(const Nonterminal& first_arg) const {
      typedef typename followup_map_t::const_iterator iter;
      iter i = followup_map_.find(first_arg);
      if (i != followup_map_.end()) {
        return i->second;
      } else {
        // Return empty map.
        static const nt_set_map_t empty_map_;
        return empty_map_;
      }
    }
  private:
    typedef std::map<Nonterminal, nt_set_map_t> followup_map_t;
    /** Set of nonterminals added to parser. */
    nt_set_t nonterminals_;
    /** Rules added to parser. */
    rule_vector_t rules_;
    /** Maps each nonterminal to its searches. */
    nt_set_map_t search_map_;
    /** Maps rhs to the set containing lhs iff lhs := rhs is a rule. */
    nt_set_map_t enext_;
    /** Maps each pair of Nonterminals (lhs, first_arg) to its followups. */
    followup_map_t followup_map_;
  };

  template<typename Nonterminal>
  class earley_set_t;

  template<typename Nonterminal>
  std::ostream&
  operator<<(std::ostream& o, const earley_set_t<Nonterminal>& s);

  /**
   * Structure identifying starting index and position of a nonterminal
   * that may be generated.
   */
  template<typename Nonterminal>
  struct prefix_pair_t {
    typedef boost::shared_ptr< earley_set_t<Nonterminal> > set_ptr;

    prefix_pair_t(const set_ptr& aset, Nonterminal ant)
      : set(aset),
        nt(ant) {
    }

    set_ptr set;
    Nonterminal nt;
  };

  /** Compares prefix pairs. */
  template<typename Nonterminal>
  bool operator<(const prefix_pair_t<Nonterminal>& x,
                 const prefix_pair_t<Nonterminal>& y) {
    return (x.set < y.set)
        || (x.set == y.set) && (x.nt < y.nt);
  }

  /** Writes prefix pair to stream for debugging purposes. */
  template<typename Nonterminal>
  std::ostream&
  operator<<(std::ostream& o, const prefix_pair_t<Nonterminal>& pair) {
    return o << "(" << pair.start << ", " << pair.nt << ")";
  }

  template<typename Nonterminal>
  class pending_map_t {
  public:
    void add(const boost::shared_ptr< earley_set_t<Nonterminal> >& set,
             const Nonterminal& lhs,
             const Nonterminal& second_arg) {
      map_[second_arg].insert(prefix_pair_t<Nonterminal>(set, lhs));
    }

    /**
     * Returns a set containing pairs (i, state) identifying a substring
     * starting at position i that is generated by lhs if the argument
     * generates a string after this set.
     */
    const std::set< prefix_pair_t<Nonterminal> >&
    operator[](const Nonterminal& second_arg) const {
      typedef typename map_t::const_iterator iter;
      iter i = map_.find(second_arg);
      if (i != map_.end()) {
        return i->second;
      } else {
        static const pair_set_t empty_set_;
        return empty_set_;
      }
    }

  private:
    typedef std::set<prefix_pair_t<Nonterminal> > pair_set_t;
    typedef std::map<Nonterminal, pair_set_t> map_t;

    map_t map_;
  };

  /**
   * Maintains parsing information for a specific string index needed by
   * Earley algorithm.
   */
  template<typename Nonterminal>
  class earley_set_t {
  public:
    typedef std::set<prefix_pair_t<Nonterminal> > pending_set_t;
    //typedef std::map<Nonterminal, pending_set_t> pending_map_t;
    typedef boost::shared_ptr<earley_set_t<Nonterminal> > set_ptr;

    earley_set_t(const std::set<Nonterminal>& searches)
      : searches_(searches) {
    }

    earley_set_t(const std::set<Nonterminal>& searches,
                 const pending_map_t<Nonterminal>& pending_map)
      : searches_(searches),
        pending_map_(pending_map) {
    }

    /** Returns nonterminals this set is starting to search for. */
    const std::set<Nonterminal>& searches(void) const {
      return searches_;
    }

    /**
     * Returns a map from nonterminals to the pendings for that
     * nonterminal.
     */
    const pending_map_t<Nonterminal>& pending_map(void) const {
      return pending_map_;
    }
  private:
    // Disable copy construction and assignment.
    earley_set_t(const earley_set_t<Nonterminal>&);
    earley_set_t<Nonterminal>& operator=(const earley_set_t<Nonterminal>&);

    friend
    std::ostream&
    operator<<<>(std::ostream& o, const earley_set_t<Nonterminal>& s);

    /** Set of nonterminals we are searching for. */
    std::set<Nonterminal> searches_;
    /**
     * Maps each nonterminals alpha to (start index, nonterminal pairs) that
     * are accepted alpha is accepted later on.
     */
    pending_map_t<Nonterminal> pending_map_;
  };

  template<typename InputIterator>
  void print_each(std::ostream& o, InputIterator begin, InputIterator end) {
    for (InputIterator i = begin; i != end; ++i)
      o << ((i != begin) ? ", " : "") << *i;
  }

  template<typename InputIterator>
  void print_each_pending(std::ostream& o,
                          InputIterator begin, InputIterator end) {
    for (InputIterator i = begin; i != end; ++i) {
      o << ((i != begin) ? ", " : "")
        << "[" << i->first << " -> {";
      print_each(o, i->second.begin(), i->second.end());
      o << "}]";
    }
  }

  /**
   * Writes Earley set to output stream for debugging purposes.
   * \relates earley_set_t
   */
  template<typename Nonterminal>
  std::ostream&
  operator<<(std::ostream& o, const earley_set_t<Nonterminal>& s) {
    o << "searches: {";
    print_each(o, s.searches_.begin(), s.searches_.end());
    o << "} pendings: {";
    print_each_pending(o, s.pendings_.begin(), s.pendings_.end());
    o << "}";
    return o;
  }

  /** The trace formed from Earley's parsing algorithm. */
  template<typename Nonterminal>
  class earley_trace_t {
  public:
    typedef boost::shared_ptr<earley_set_t<Nonterminal> > set_ptr;

    /**
     * Construct an empty earley trace that starts searching for all
     * nonterminals in rules.
     */
    earley_trace_t(const chomsky_rules_t<Nonterminal>& rules) {
      sets_.push_back(set_ptr(
                new earley_set_t<Nonterminal>(rules.nonterminals())));
    }

    /**
     * Construct an empty earley trace that starts searching for given
     * nonterminals.
     */
    earley_trace_t(const chomsky_rules_t<Nonterminal>& rules,
                   const Nonterminal& nt) {
      std::set<Nonterminal> searches;
      rules.add_and_close_searches(searches, nt);
      sets_.push_back(set_ptr(new earley_set_t<Nonterminal>(searches)));
    }

    /** Returns size of trace. */
    size_t size(void) const {
      return sets_.size();
    }

    /** Returns the ith earley set in trace. */
    const set_ptr& operator[](size_t i) const {
      if ((i < 0) || (sets_.size() <= i))
        throw std::logic_error("Index out of range.");
      return sets_[i];
    }

    /** Returns an Earley trace from start_index to the end. */
    earley_trace_t<Nonterminal> suffix(size_t start_index) const {
      return earley_trace_t<Nonterminal>(*this, start_index);
    }

    /** Pushes new Earley set to end. */
    void push_back(const set_ptr& set) {
      sets_.push_back(set);
    }

    /** Returns last Earley set. */
    const set_ptr& back(void) const {
      return sets_.back();
    }

    /** Removes last Earley set from end. */
    void pop_back(void) {
      sets_.pop_back();
    }
  private:
    /**
     * Construct an empty earley trace that starts searching for the
     * nonterminals being searched for in the given set.
     */
    earley_trace_t(const earley_trace_t<Nonterminal>& trace,
                   size_t start_index)
      : sets_(trace.sets_.begin() + start_index, trace.sets_.end()) {
    }

    std::vector<set_ptr> sets_;
  };

  /** Terminal rules for a CFG. */
  template<typename Terminal, typename Nonterminal>
  class terminal_rules_t {
  public:
    /**
     * Adds new terminal symbol that can be generated by given nonterminals
     * to parser.
     */
    template<typename Iterator>
    void add_terminal(const Terminal& terminal,
                      Iterator nt_begin, Iterator nt_end) {
      generator_map_.insert(make_pair(terminal, nt_set_t(nt_begin, nt_end)));
    }

    /** Returns the nonterminals that generate a specific terminal. */
    const std::set<Nonterminal>& generators(const Terminal& t) const {
      return generator_map_.find(t)->second;
    }
  private:
    /** Set of nonterminals. */
    typedef std::set<Nonterminal> nt_set_t;
    typedef std::map<Terminal, nt_set_t> generator_map_t;
    /** Maps each terminal to its generators. */
    generator_map_t generator_map_;
  };


  /**
   * Updates pendings and searches given a parsed string and the
   * nonterminals that were being searched for in the old set.
   */
  template<typename Nonterminal>
  void add_all_pendings(const chomsky_rules_t<Nonterminal>& rules,
                        std::set<Nonterminal>& searches,
                        pending_map_t<Nonterminal>& pending,
                        const std::set<Nonterminal>& old_searches,
                        prefix_pair_t<Nonterminal> parsed_string) {
    typedef std::set<Nonterminal> nt_set_t;
    typedef std::map<Nonterminal, nt_set_t> nt_set_map_t;
    typedef typename nt_set_t::const_iterator set_iter;
    typedef typename nt_set_map_t::const_iterator map_iter;

    boost::shared_ptr< earley_set_t<Nonterminal> > start_set
          = parsed_string.set;
    const Nonterminal& gen_nt = parsed_string.nt;
    const nt_set_map_t& map = rules.followups(gen_nt);

    set_iter iset = old_searches.begin();
    set_iter old_end = old_searches.end();
    map_iter imap = map.begin();
    map_iter map_end = map.end();
    while ((iset != old_end) && (imap != map_end)) {
      if (*iset == imap->first) {
        const Nonterminal& lhs = *iset;
        const std::set<Nonterminal>& seconds = imap->second;
        for (set_iter i = seconds.begin(); i != seconds.end(); ++i) {
          pending.add(start_set, lhs, *i);
          rules.add_and_close_searches(searches, *i);
        }
        ++iset;
        ++imap;
      } else if (*iset < imap->first) {
        ++iset;
      } else {
        ++imap;
      }
    }
  }

  /**
   * Perform scanning to determine which nonterminals we were searching for
   * in the previous trace are nonterminals that match the current character.
   * The generated nonterminals will be closed with respect to unary rules.
   */
  template<typename Nonterminal, typename NonterminalIterator>
  void scan(ceta::impl::qcontainer_t<
               std::set< prefix_pair_t<Nonterminal> > >& gen,
            const boost::shared_ptr<earley_set_t<Nonterminal> >& prev_set,
            const std::set<Nonterminal>& prev_searches,
            NonterminalIterator found_begin,
            NonterminalIterator found_end) {
    for (NonterminalIterator i = found_begin; i != found_end; ++i) {
      // If current nonterminal was being searched for.
      if (prev_searches.count(*i) > 0)
        gen.insert(prefix_pair_t<Nonterminal>(prev_set, *i));
    }
  }

  /**
   * Advances trace by one terminal in order to continue parsing.
   * Returns the set of substrings that where recognized starting from
   * a given state and ending after last terminal.
   */
  template<typename Nonterminal, typename NonterminalIterator>
  std::set< prefix_pair_t<Nonterminal> >
  parse(const chomsky_rules_t<Nonterminal>& rules,
        earley_trace_t<Nonterminal>& trace,
        NonterminalIterator found_begin,
        NonterminalIterator found_end) {
    typedef prefix_pair_t<Nonterminal> pre_pair_t;
    typedef std::set<pre_pair_t> gen_set_t;
    typedef earley_set_t<Nonterminal> set_t;
    typedef boost::shared_ptr<set_t > set_ptr;

    ceta::impl::qcontainer_t<gen_set_t> gen;
    // Get most recent trace set.
    // Add generated results from scaning current character.
    scan(gen, trace.back(), trace.back()->searches(),
         found_begin, found_end);
    std::set<Nonterminal> searches;
    pending_map_t<Nonterminal> pending_map;
    while (!gen.queue_empty()) {
      const set_ptr old_set = gen.front().set;
      const Nonterminal gen_nt = gen.front().nt;
      add_all_pendings(rules, searches, pending_map, old_set->searches(),
                       gen.front());
      // Add all sets generated by epsilon rules to gen.
      {
        std::set<Nonterminal> enext_set = rules.enext(gen_nt);
        typedef typename std::set<Nonterminal>::const_iterator iter;
        for (iter i = enext_set.begin(); i != enext_set.end(); ++i)
          gen.insert(pre_pair_t(old_set, *i));
      }
      // For each pending in old_set for gen_nt.
      const gen_set_t& pset = old_set->pending_map()[gen_nt];
      gen.insert(pset.begin(), pset.end());
      gen.pop_front();
    }
    trace.push_back(set_ptr(new set_t(searches, pending_map)));
    return gen.container();
  }

  template<typename Nonterminal>
  bool accepts(const earley_trace_t<Nonterminal>& trace,
               const std::set< prefix_pair_t<Nonterminal> >& gen,
               size_t index,
               const Nonterminal& nt) {
    return gen.count(
            prefix_pair_t<Nonterminal>(trace[index], nt)) > 0;
  }

  /**
   * Returns true if nonterminal start generates the string using the grammar
   * rules.
   */
  template<typename Terminal, typename Nonterminal, typename InputIterator>
  bool member(const chomsky_rules_t<Nonterminal>& rules,
              const terminal_rules_t<Terminal, Nonterminal>& trules,
              const Nonterminal& start,
              InputIterator string_begin, InputIterator string_end) {
    // Create trace with single element for before string has started
    // processing.
    earley_trace_t<Nonterminal> trace(rules, start);

    std::set< prefix_pair_t<Nonterminal> > gen;
    // For each character in string
    for (InputIterator i = string_begin; i != string_end; ++i) {
      const std::set<Nonterminal>& found = trules.generators(*i);
      gen = parse(rules, trace, found.begin(), found.end());
    }
    // Determine if last set in trace recognized start.
    return accepts(trace, gen, 0, start);
  }
}}
#endif
