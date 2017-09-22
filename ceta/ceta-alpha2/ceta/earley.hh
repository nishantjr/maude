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
#ifndef _earley_hh_
#define _earley_hh_

#include <map>
#include <ostream>
#include <set>
#include <stdexcept>
#include <utility>
#include <vector>

#include "qcontainer.hh"

//TODO: Cite Practical Earley parsing paper to explain scanning, predictor,
// and completer terminology.

namespace ceta {
namespace cfg {
  template<typename Nonterminal>
  class earley_set_t;

  template<typename Nonterminal>
  std::ostream&
  operator<<(std::ostream& o, const earley_set_t<Nonterminal>& s);

  /** An Earley set identifies  */
  template<typename Nonterminal>
  class earley_set_t {
  public:
    typedef std::pair<size_t, Nonterminal> prefix_pair_t;
    typedef std::set<prefix_pair_t> pending_set_t;
    typedef std::map<Nonterminal, pending_set_t> pending_map_t;

    /** Returns nonterminals this set is starting to search for. */
    const std::set<Nonterminal>& searchings(void) const {
      return searchings_;
    }

    /** Add each element in collection as nonterminal to search for. */
    template<typename NonterminalIterator>
    void add_searching(NonterminalIterator nt_begin,
                       NonterminalIterator nt_end) {
      searchings_.insert(nt_begin, nt_end);
    }

    /** 
     * Returns a set containing each pair (i, lhs) such that a string
     * starting at position i and ending at position j is recognized by
     * nonterminal lhs if rhs2 is recognized by a string ending at position
     * j.
     */
    const std::set< std::pair<size_t, Nonterminal> >&
    pendings(const Nonterminal& second_arg) const {
      typedef typename pending_map_t::const_iterator iter;
      iter i = pendings_.find(second_arg);
      if (i != pendings_.end()) {
        return i->second;
      } else {
        static const pending_set_t empty_set_;
        return empty_set_;
      }
    }

    /** Adds an element to pending set. */
    void add_pending(size_t start_index,
                     const Nonterminal& lhs,
                     const Nonterminal& second_arg) {
      pendings_[second_arg].insert(std::make_pair(start_index, lhs));
    }

    /**
     * Returns a map from nonterminals to the pendings for that
     * nonterminal.
     */
    const pending_map_t& pending_map(void) const {
      return pendings_;
    }
      
  private:
    friend
    std::ostream&
    operator<<<>(std::ostream& o, const earley_set_t<Nonterminal>& s);

    /** Set of nonterminals we are searching for. */
    std::set<Nonterminal> searchings_;
    
    /**
     * Mapping from second argument in right hand side to pending pairs 
     * identifying starting index and left-hand side that would be generated.
     */
    pending_map_t pendings_;
  };

  template<typename InputIterator>
  void print_each(std::ostream& o, InputIterator begin, InputIterator end) {
    for (InputIterator i = begin; i != end; ++i) {
      if (i != begin)
        o << ", ";
      o << *i;
    }
  }

  template<typename InputIterator>
  void print_each_pair(std::ostream& o,
                       InputIterator begin, InputIterator end) {
    for (InputIterator i = begin; i != end; ++i) {
      if (i != begin)
        o << ", ";
      o << "(" << i->first << ", " << i->second << ")";
    }
  }

  template<typename InputIterator>
  void print_each_pending(std::ostream& o,
                          InputIterator begin, InputIterator end) {
    for (InputIterator i = begin; i != end; ++i) {
      if (i != begin)
        o << ", ";
      o << "[" << i->first << " -> {";
      print_each_pair(o, i->second.begin(), i->second.end());
      o << "}]";
    }
  }

  template<typename Nonterminal>
  std::ostream&
  operator<<(std::ostream& o, const earley_set_t<Nonterminal>& s) {
    o << "searchings: {";
    print_each(o, s.searchings_.begin(), s.searchings_.end());
    o << "} pendings: {";
    print_each_pending(o, s.pendings_.begin(), s.pendings_.end());
    o << "}";
    return o;
  }

  /**
   * This returns a copy of the Earley set whose pending timestamps have
   * been decremented by difference.  If this results in a pending event
   * with a negative timestamp, then that event is not added to the result.
   */
  template<typename Nonterminal>
  const earley_set_t<Nonterminal>
  shift_events(const earley_set_t<Nonterminal>& set, size_t difference) {
    earley_set_t<Nonterminal> result;
    result.add_searching(set.searchings().begin(), set.searchings().end());
    
    typedef std::set< std::pair<size_t, Nonterminal> > pending_set_t;
    typedef std::map<Nonterminal, pending_set_t> pending_map_t;
    const pending_map_t& pending_map = set.pending_map();
    typedef typename pending_map_t::const_iterator map_iter;
    for (map_iter i = pending_map.begin(); i != pending_map.end(); ++i) {
      const Nonterminal& second_arg = i->first;
      const pending_set_t& cur_set = i->second;
        
      typedef typename pending_set_t::const_iterator set_iter;
      for (set_iter i = cur_set.begin(); i != cur_set.end(); ++i) {
        size_t cur_start = i->first;
        const Nonterminal& lhs = i->second;
        if (cur_start >= difference) 
          result.add_pending(cur_start - difference, lhs, second_arg);
      }
    }
    return result;
  }

  /** The trace formed from Earley's parsing algorithm. */
  template<typename Nonterminal>
  class earley_trace_t {
  public:
    /**
     * Construct an empty earley trace that starts searching for given
     * nonterminals.
     */
    template<typename NonterminalIterator>
    earley_trace_t(NonterminalIterator nt_begin,
                   NonterminalIterator nt_end) {
      sets_.push_back(earley_set_t<Nonterminal>());
      sets_[0].add_searching(nt_begin, nt_end);
    }

    /** Returns size of trace. */
    size_t size(void) const {
      return sets_.size();
    }
    
    /** Returns the ith earley set in trace. */
    const earley_set_t<Nonterminal>& operator[](size_t i) const {
      if ((i < 0) || (sets_.size() <= i))
        throw std::logic_error("Index out of range.");
      return sets_[i];
    }

    /** Returns an Earley trace from start_index to the end. */
    earley_trace_t<Nonterminal> suffix(size_t start_index) const {
      const std::set<Nonterminal>& set = sets_[start_index].searchings();
      
      earley_trace_t<Nonterminal> result(set.begin(), set.end());
      result.sets_.reserve(sets_.size() - start_index);
      for (size_t i = start_index + 1; i != sets_.size(); ++i)
        result.push_back(shift_events(sets_[i], start_index));
      return result;
    }

    /** Pushes new Earley set to end. */
    void push_back(const earley_set_t<Nonterminal>& set) {
      sets_.push_back(set);
    }

    /** Returns last Earley set. */
    const earley_set_t<Nonterminal>& back(void) const {
      return sets_.back();
    }

    /** Removes last Earley set from end. */
    void pop_back(void) {
      sets_.pop_back();
    }
  private:
    std::vector<earley_set_t<Nonterminal> > sets_;
  };

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

  template<typename Nonterminal>
  class chomsky_rules_t {
  public:
    /** Construct empty set of chomsky rules. */
    chomsky_rules_t(void) {
    }
    /** Construct chomsky rules with given nonterminals and rules. */
    template<typename NonterminalIterator, typename RuleIterator>
    chomsky_rules_t(NonterminalIterator nt_begin,
                    NonterminalIterator nt_end,
                    RuleIterator rules_begin,
                    RuleIterator rules_end) {
      for (NonterminalIterator i = nt_begin; i != nt_end; ++i)
        add_nonterminal(*i);
      for (RuleIterator i = rules_begin; i != rules_end; ++i)
        add_rule(i->lhs, i->first, i->second);
    }
      
    /** Adds new nonterminal symbol to parser. */
    void add_nonterminal(const Nonterminal& nt) {
      nonterminals_.insert(nt);
      search_map_.insert(make_pair(nt, nt_set_t(&nt, &nt + 1)));
    }

    /** Adds a rule from a nonterminal to two nonterminals. */
    void add_rule(const Nonterminal& lhs,
                  const Nonterminal& first_arg,
                  const Nonterminal& second_arg) {
      search_map_[lhs].insert(first_arg);
      followup_map_[first_arg][lhs].insert(second_arg);
    }
  
    /** Returns set of nonterminals. */
    const std::set<Nonterminal>& nonterminals(void) const {
      return nonterminals_;
    }

    /**
     * Return nonterminals that we should start searching for if we start
     * searching for the given nonterminal.  This set contains lhs along
     * with every nonterminal that is the first argument of a rule with the
     * given left-hand-side
     */
    const std::set<Nonterminal>& searches(const Nonterminal& lhs) const {
      return search_map_.find(lhs)->second;
    }

    /** Map from nonterminals to set of nonterminals. */
    typedef std::map<Nonterminal, std::set<Nonterminal> > nt_set_map_t;

    /** 
     * Returns a map that pairs nonterminals that appear on the 
     * left-hand-side of a rule with the nonterminals that appear
     * as the second argument on the right-hand-side of a rule whose first
     * argument is the given nonterminal.
     */
    const nt_set_map_t&
    followups(const Nonterminal& first_arg) const {
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

    /**
     * Return nonterminals that appear as the second argument in a rrule with
     * the given left-hand-side and first argument.
     */
    const std::set<Nonterminal>& 
    followups(const Nonterminal& lhs, const Nonterminal& first_arg) const {
      const nt_set_map_t& map = followups(first_arg);
      typedef typename nt_set_map_t::const_iterator iter;
      iter i = map.find(lhs);
      if (i != map.end()) {
        return i->second;
      } else {
        // Return empty set.
        static const nt_set_t empty_set_;
        return empty_set_;
      }
    }
  private:
    /** Set of nonterminals. */
    typedef std::set<Nonterminal> nt_set_t;
    typedef std::map<Nonterminal, nt_set_t> search_map_t;
    typedef std::map<Nonterminal, nt_set_map_t> followup_map_t;
    /** Set of nonterminals added to parser. */
    nt_set_t nonterminals_;
    /** Maps each nonterminal to its searches. */
    search_map_t search_map_;
    /** Maps each pair of Nonterminals (lhs, first_arg) to its followups. */
    followup_map_t followup_map_;
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
   * Adds a pending with start_index, lhs and each followup for lhs and
   * first_arg.
   */
  template<typename Nonterminal>
  void add_all_pendings(const chomsky_rules_t<Nonterminal>& rules,
                        earley_set_t<Nonterminal>& set,
                        size_t start_index, 
                        const Nonterminal& lhs,
                        const Nonterminal& first_arg) {
    const std::set<Nonterminal>& f = rules.followups(lhs, first_arg);
    typedef typename std::set<Nonterminal>::const_iterator iter;
    for (iter i = f.begin(); i != f.end(); ++i) {
      set.add_pending(start_index, lhs, *i);
      // Add each thing to search for if *i is not already added.
      if (set.searchings().count(*i) == 0) {
        const std::set<Nonterminal>& searches = rules.searches(*i);
        set.add_searching(searches.begin(), searches.end());
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
               std::set< std::pair<size_t, Nonterminal> > >& gen,
            size_t prev_index,
            const std::set<Nonterminal>& prev_searchings,
            NonterminalIterator found_begin,
            NonterminalIterator found_end) {
    for (NonterminalIterator i = found_begin; i != found_end; ++i) {
      // If current nonterminal was being searched for.
      if (prev_searchings.count(*i) > 0)
        gen.insert(make_pair(prev_index, *i));
    }
  }

  /**
   * Advances trace by one terminal in order to continue parsing.
   * Returns the set of substrings that where recognized starting from
   * a given state and ending after last terminal. 
   */
  template<typename Nonterminal, typename NonterminalIterator>
  std::set< std::pair<size_t, Nonterminal> >
  parse(const chomsky_rules_t<Nonterminal>& rules,
        earley_trace_t<Nonterminal>& trace,
        NonterminalIterator found_begin,
        NonterminalIterator found_end) {
    typedef std::pair<size_t, Nonterminal> gen_pair_t;
    typedef std::set<gen_pair_t> gen_set_t;

    ceta::impl::qcontainer_t<gen_set_t> gen;
    // Get most recent trace set.
    // Add generated results from scaning current character.
    scan(gen, trace.size() - 1, trace.back().searchings(),
         found_begin, found_end);
    earley_set_t<Nonterminal> next_set;
    while (!gen.queue_empty()) {
      size_t gen_start = gen.front().first;
      const Nonterminal gen_nt = gen.front().second;
      const earley_set_t<Nonterminal>& old_set = trace[gen_start];
      // For each nonterminal old_set started searching for.
      typedef typename std::set<Nonterminal>::const_iterator nt_iter;
      nt_iter old_s_end = old_set.searchings().end();
      for (nt_iter i = old_set.searchings().begin(); i != old_s_end; ++i) {
        // Add pending sets for lhs *i and first arg gen_nt
        add_all_pendings(rules, next_set, gen_start, *i, gen_nt);
      }
      // For each pending in old_set for gen_nt.
      typedef std::set<std::pair<size_t, Nonterminal> > pset_t;
      typedef typename pset_t::const_iterator pset_iter;
      const pset_t& pset = old_set.pendings(gen_nt);
      for (pset_iter i = pset.begin(); i != pset.end(); ++i)
        gen.insert(*i);
      gen.pop_front();
    }
    trace.push_back(next_set);
    return gen.container();
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
    const std::set<Nonterminal>& searches = rules.searches(start);
    earley_trace_t<Nonterminal> trace(searches.begin(), searches.end());

    std::set< std::pair<size_t, Nonterminal> > gen;
    // For each character in string
    for (InputIterator i = string_begin; i != string_end; ++i) {
      const std::set<Nonterminal>& found = trules.generators(*i);
      gen = parse(rules, trace, found.begin(), found.end());
    }
    // Determine if last set in trace recognized start.
    return gen.count(make_pair(0, start)) > 0;
  }
}}
#endif
