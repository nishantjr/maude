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
#ifndef _fa_hh_
#define _fa_hh_

#include <deque>
#include <map>
#include <ostream>
#include <set>
#include <stdexcept>
#include <vector>

#include <boost/optional/optional.hpp>
#include <boost/shared_ptr.hpp>

namespace ceta {
namespace fa {

/** Stores a set of finite automaton transition rules. */
template<typename Symbol, typename State>
class rule_set_t {
public:
  /** Adds a rule to the rule set. */
  void add(const State& lhs, const Symbol& sym, const State& rhs) {
    map_[sym][lhs].insert(rhs);
  }

  /**
   * Return the next states reachable from a state in the lhs using a
   * transition involving sym.
   */
  const std::set<State>
  next_states(const std::set<State>& lhs, const Symbol& sym) const {
    // Lookup rules for symbol.
    typedef typename map_t::const_iterator map_iter;
    map_iter cur_map = map_.find(sym);
    if (cur_map == map_.end())
      return std::set<State>();
    // Rules for symbol.
    const symbol_map_t& sym_rules = cur_map->second;

    // Build set of next states
    std::set<State> result;
    // For each state in lhs
    typedef typename std::set<State>::const_iterator state_iter;
    state_iter lhs_end = lhs.end();
    for (state_iter i = lhs.begin(); i != lhs_end; ++i) {
      // Get next states for each state on lhs side.
      typedef typename symbol_map_t::const_iterator rule_iter;
      rule_iter irules = sym_rules.find(*i);
      // Add next states to result.
      if (irules != sym_rules.end())
        result.insert(irules->second.begin(), irules->second.end());
    }
    return result;
  }
private:
  /** Map from a state to set of states reachable for a specific symbol. */
  typedef std::map<State, std::set<State> > symbol_map_t;
  /** Map from symbol to rules for that symbol. */
  typedef std::map<Symbol, symbol_map_t> map_t;

  /** Map from each symbol to transitions involving symbol. */
  map_t map_;
};

/** A reachable subset. */
template<typename Symbol, typename State>
class subset_t {
public:
  /** Construct an initial subset. */
  template<typename StateIterator>
  subset_t(StateIterator states_begin, StateIterator states_end)
    : impl_(new impl_t(states_begin, states_end)) {
  }

  /** Construct a subset from a previous subset. */
  template<typename StateIterator>
  subset_t(const subset_t<Symbol, State>& previous,
           const Symbol& symbol,
           StateIterator states_begin,
           StateIterator states_end)
    : impl_(new impl_t(previous.impl_, symbol, states_begin, states_end)) {
  }

  /** Returns true if a previous subset was used to reach this subset. */
  bool has_previous(void) const {
    return impl_->previous != NULL;
  }
  /** Returns previus subset used to reach this subset if any. */
  const subset_t<Symbol, State> previous(void) const {
    //TODO: Consider throwing logic error here.
    return subset_t<Symbol, State>(impl_->previous);
  }
  /** Returns symbol used from previous subset to reach here if any. */
  const Symbol& symbol(void) const {
    //TODO: Consider throwing logic error here.
    return *(impl_->symbol);
  }
  /** Returns states reachable at this subset. */
  const std::set<State>& states(void) const {
    return impl_->states;
  }
private:
  /** An implementation record for a subset. */
  struct impl_t {
    /** Construct an initial implementation record. */
    template<typename StateIterator>
    impl_t(StateIterator states_begin, StateIterator states_end)
      : states(states_begin, states_end) {
    }
    /** Construct a successor implementation record. */
    template<typename StateIterator>
    impl_t(const boost::shared_ptr<impl_t>& previous_arg,
           const Symbol& symbol_arg,
           StateIterator states_begin,
           StateIterator states_end)
      : previous(previous_arg),
        symbol(symbol_arg),
        states(states_begin, states_end) {
    }
    /** Pointer to previous implementation. */
    boost::shared_ptr<impl_t> previous;
    /** Symbol used to reach this subset from previous. */
    boost::optional<Symbol> symbol;
    /** Set of states reached. */
    std::set<State> states;
  };

  /** Construct a subset from a pointer to its implementation. */
  subset_t(const boost::shared_ptr<impl_t>& impl)
    : impl_(impl) {
  }

  /** Pointer to implementation record for this subset. */
  boost::shared_ptr<impl_t> impl_;
};

/** Write subset to output stream. */
template<typename Symbol, typename State>
std::ostream&
operator<<(std::ostream& o, const subset_t<Symbol, State>& subset) {
  o << "String: ";
  std::deque<Symbol> prev_string;
  const subset_t<Symbol, State> cur_subset = subset;
  while (cur_subset.has_previous()) {
    prev_string.push_front(cur_subset.symbol());
    cur_subset = cur_subset->previous();
  }
  typedef typename std::deque<Symbol>::const_iterator sym_iter;
  for (sym_iter i = prev_string.begin(); i != prev_string.end(); ++i) {
    if (i != prev_string.begin())
      o << " ";
    o << *i;
  }
  o << "; Set: {";
  typedef typename std::set<State>::const_iterator state_iter;
  state_iter states_end = subset.states().end();
  for (state_iter i = subset.states().begin(); i != states_end; ++i) {
    if (i != subset.states().begin())
      o << ", ";
    o << *i;
  }
  o << "}";
  return o;
}

/**
 * An interface to an incremental finite automaton subset contruction
 * algorithm.
 */
template<typename Symbol, typename State>
class subset_constructor_t {
public:
  /**
   * Constructs a new subset constructor with the given symbols, rules, and
   * initial states.
   */
  template<typename SymbolIterator,
           typename StateIterator>
  subset_constructor_t(const rule_set_t<Symbol, State>& rules,
                       SymbolIterator symbols_begin,
                       SymbolIterator symbols_end,
                       StateIterator states_begin,
                       StateIterator states_end)
    : rules_(rules),
      symbols_(symbols_begin, symbols_end),
      cur_symbol_(symbols_.begin()) {
    // Initialize pending explorations with initial states.
    next_ = add_subset(subset_t<Symbol, State>(states_begin, states_end));
    cur_symbol_ = symbols_.begin();
  }

  /** Returns true if there are more new subsets that should be returned. */
  bool has_next() {
    while ((next_ == reachables_.end()) && !pending_.empty()) {
      const subset_t<Symbol, State>& cur_subset = pending_.front()->second;
      // Explore from current subset using next symbols.
      while ((next_ == reachables_.end())
          && (cur_symbol_ != symbols_.end())) {
        // Get new states from currrent subset after transitioning with
        // current symbol.
        const std::set<State> new_states
            = rules_.next_states(cur_subset.states(), *cur_symbol_);
        // Add to reachable states if new.
        if (reachables_.count(new_states) == 0) {
          next_ = add_subset(subset_t<Symbol, State>(cur_subset,
                  *cur_symbol_, new_states.begin(), new_states.end()));
        }
        ++cur_symbol_;
      }
      // Goto next pending symbol if we have not found anything new.
      if (next_ == reachables_.end()) {
        pending_.pop_front();
        cur_symbol_ = symbols_.begin();
      }
    }
    return next_ != reachables_.end();
  }

  /** Returns next subset found if any. */
  const subset_t<Symbol, State>& next() {
    if (has_next()) {
      return next_->second;
    } else {
      throw std::logic_error("No next subset.");
    }
  }
  /** Pops the next subset from the queue. */
  void pop_next() {
    next_ = reachables_.end();
  }
private:
  typedef std::map<std::set<State>, subset_t<Symbol, State> >
          reachable_map_t;
  typedef typename reachable_map_t::const_iterator reachable_iter;
  typedef typename std::vector<Symbol>::const_iterator sym_iter;

  /** Adds a new subset to reachable states and pendings. */
  reachable_iter add_subset(const subset_t<Symbol, State>& subset) {
    reachable_iter result =
          reachables_.insert(std::make_pair(subset.states(), subset)).first;
    pending_.push_back(result);
    return result;
  }

  /** Set of transition rules. */
  rule_set_t<Symbol, State> rules_;
  /** Set of symbols we are exploring from. */
  std::vector<Symbol> symbols_;
  /** Map from each reachable set of states to element for that state. */
  reachable_map_t reachables_;
  /** Pending elements to be explored. */
  std::deque<reachable_iter> pending_;
  /** Symbol that should explore head of pending_ next. */
  sym_iter cur_symbol_;
  /** Next reachable set to return. */
  reachable_iter next_;
};

}}
#endif
