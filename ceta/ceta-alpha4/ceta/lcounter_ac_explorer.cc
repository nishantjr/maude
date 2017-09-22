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

//DONE:
//1. Finish explore_next for lcounter_t
//2. Implement operator< for term_t
//3. Fix lcounter_t.initialize_symbol_values.
//4. Implement add in counter_set_t
//5. Implement initial_state in lcounter_t
//6. Implement add_rule in lcounter_t
//7. Fix bug in selecting/deselecting symbols.
//8. Implement is_accepting in lcounter_t
//9. Implement operator< in lcounter_t.
//10. Fix add_reachable to use image.
//11. Update to use new closure interface.
//
#include "lcounter_ac_explorer.hh"
#include <iostream>

#include "reachable_image.hh"

namespace ceta {
namespace lcounter {
  void sig_error(const std::string& s) NO_RETURN;
  void sig_error(const std::string& s) {
    int* x = 0;
    *x = 123;
    throw std::logic_error(s);
  }

  static
  bool is_odd(int value) {
    return (value & 1) == 1;
  }

  static
  bool is_even(int value) {
    return (value & 1) == 0;
  }

  /** A nonterminal or terminal symbol in CFG. */
  class symbol_t {
  public:
    template<typename Data>
    explicit symbol_t(const Data& data)
      : data_(data),
        max_bit_flip_count_(0) {
    }

    bool is_terminal(void) const {
      return boost::get<term_t>(&data_) != NULL;
    }

    bool is_nonterminal(void) const {
      return !is_terminal();
    }

    const term_t& term(void) const {
      try {
        return boost::get<term_t>(data_);
      } catch (...) {
        sig_error("bad_get");
      }
    }

    /** Returns state associated to symbol if this is a nonterminal. */
    const state_t& state(void) const {
      try {
        return boost::get<state_t>(data_);
      } catch (...) {
        sig_error("bad_get");
      }
    }

    /** Initializes symbol for use with next instance. */
    void initialize_next(int carry_value) {
      value_ = carry_value;
      bit_flip_count_ = max_bit_flip_count_;
      check_invariants();
    }

    int value(void) const {
      return value_;
    }

    bool can_flip(void) const {
      return (bit_flip_count_ > 1) || is_odd(value_);
    }

    void dec_value(void) {
      --value_;
      --bit_flip_count_;
      check_invariants();
    }

    void undo_dec_value(void) {
      ++value_;
      ++bit_flip_count_;
      check_invariants();
    }

    void inc_value(void) {
      ++value_;
      --bit_flip_count_;
      check_invariants();
    }

    void undo_inc_value(void) {
      --value_;
      ++bit_flip_count_;
      check_invariants();
    }

    /** Adds two to value of counter without changing bit_flip_count_. */
    void inc_value_twice(void) {
      value_ += 2;
    }

    /** Undoes effect of incrementing counter. */
    void undo_inc_value_twice(void) {
      value_ -= 2;
    }

    bool can_skip(void) {
      return (bit_flip_count_ > 1) || is_even(value_);
    }

    /** Skips flipping a bit. */
    void skip(void) {
      --bit_flip_count_;
      check_invariants();
    }

    void undo_skip(void) {
      ++bit_flip_count_;
      check_invariants();
    }

    /**
     * Returns the maximum number of times the least-significant bit of the
     * value can be flipped.
     */
    size_t max_bit_flip_count(void) const {
      return max_bit_flip_count_;
    }

    /**
     * Increments max number of times that the lsb of value can be flipped.
     */
    void inc_max_bit_flip_count(void) {
      ++max_bit_flip_count_;
    }

    /** Returns true if this element can propagate further. */
    bool can_propagate(void) const {
      return (max_bit_flip_count_ > 0) || ((value_ & 2) == 0);
    }

    /**
     * Checks that the invariants are satisfied and that each rule has been
     * set to true or false so that the bit_flip_count_ is now 0.
     */
    void check_assigned(void) const {
      if (bit_flip_count_ != 0)
        sig_error("bit_flip_count_ not zero");
      check_invariants();
    }

  private:
    void check_invariants(void) const {
      // Signal error if bit cannot be flipped and value_ is odd.
      if ((bit_flip_count_ == 0) && is_odd(value_)) {
        sig_error("Illegal bit-flip count");
      }
    }

    /**
     * If this is a nonterminal symbol, then data_ contains the state
     * associated to the nonterminal.  Otherwise, this is a terminal and
     * data contains the term_ which created this symbol.
     */
    boost::variant<state_t, term_t> data_;
    /**
     * Maximum number of times least-significant bit of symbol can be flipped
     * by a rule.
     */
    size_t max_bit_flip_count_;
    /**
     * Number of times remaining that least-significant bit of symbol can be
     * flipped.
     */
    size_t bit_flip_count_;
    /** Number of times symbol is created minus times symbol is consumed. */
    int value_;
  };

  std::ostream& operator<<(std::ostream& o, const symbol_t& sym) {
    if (sym.is_terminal()) {
      o << sym.term();
    } else {
      o << sym.state();
    }
    return o;
  }

  class crule_t {
  public:
    /** Construct a new crule_t */
    crule_t(symbol_t* lhs, symbol_t* rhs1, symbol_t* rhs2)
      : lhs_(lhs),
        rhs1_(rhs1),
        rhs2_(rhs2),
        selected_(false) {
      // Increment sum on left and right side.
      if (lhs == rhs1) {
        if (rhs2) rhs2->inc_max_bit_flip_count();
      } else if (lhs == rhs2) {
        // If lhs != rhs1 /\ lhs == rhs2
        if (rhs1) rhs1->inc_max_bit_flip_count();
      } else if (rhs1 == rhs2) {
        // If lhs != rhs1 /\ rhs1 = rhs2
        if (lhs) lhs->inc_max_bit_flip_count();
      } else { // lhs != rhs1 /\ lhs != rhs2 /\ rhs1 != rhs2
        if (lhs) lhs->inc_max_bit_flip_count();
        if (rhs1) rhs1->inc_max_bit_flip_count();
        if (rhs2) rhs2->inc_max_bit_flip_count();
      }
    }

    /** Returns true if this rule is of the form terminal := nil. */
    bool is_terminal(void) const {
      return lhs_ && lhs_->is_terminal();
    }

    const symbol_t* lhs(void) const {
      return lhs_;
    }

    const symbol_t* rhs1(void) const {
      return rhs1_;
    }

    const symbol_t* rhs2(void) const {
      return rhs2_;
    }

    /** Returns true if rule has been selected. */
    bool selected(void) const {
      return selected_;
    }

    /**
     * Attempt to select rule.  This may fail if selecting this rule would
     * violate the invariants on symbols.  Returns true if selection is
     * sucessful.
     */
    bool try_select(void) {
      bool result;
      if (lhs_ == rhs1_) {
        result = !rhs2_ || rhs2_->can_flip();
        if (result) {
          if (rhs2_) rhs2_->inc_value();
        }
      } else if (lhs_ == rhs2_) {
        result = !rhs1_ || rhs1_->can_flip();
        if (result) {
          if (rhs1_) rhs1_->inc_value();
        }
      } else if (rhs1_ == rhs2_) {
        result = !lhs_ || lhs_->can_flip();
        if (result) {
          if (lhs_)  lhs_->dec_value();
          if (rhs1_) rhs1_->inc_value_twice();
        }
      } else { // All three symbols distinct
        result = (!lhs_ || lhs_->can_flip())
              && (!rhs1_ || rhs1_->can_flip())
              && (!rhs2_ || rhs2_->can_flip());
        if (result) {
          if (lhs_) lhs_->dec_value();
          if (rhs1_) rhs1_->inc_value();
          if (rhs2_) rhs2_->inc_value();
        }
      }
      if (result) selected_ = true;
      return result;
    }

    /**
     * Attempt to deselect rule.  This may fail if deselecting this rule
     * would violate the invariants on symbols.  Returns true if deselection
     * is successful.
     */
    bool try_deselect(void) {
      bool result;
      if (lhs_ == rhs1_) {
        result = !rhs2_ || rhs2_->can_skip();
        if (result && rhs2_) rhs2_->skip();
      } else if (lhs_ == rhs2_) {
        result = !rhs1_ || rhs1_->can_skip();
        if (result && rhs1_) rhs1_->skip();
      } else if (rhs1_ == rhs2_) {
        result = (!lhs_ || lhs_->can_skip());
        if (result && lhs_) lhs_->skip();
      } else { // All three symbols distinct
        result = (!lhs_ || lhs_->can_skip())
              && (!rhs1_ || rhs1_->can_skip())
              && (!rhs2_ || rhs2_->can_skip());
        if (result) {
          if (lhs_) lhs_->skip();
          if (rhs1_) rhs1_->skip();
          if (rhs2_) rhs2_->skip();
        }
      }
      return result;
    }


    /** Undo last selection action. */
    void undo_selection(void) {
      if (selected_) {
        if (lhs_ == rhs1_) {
          if (rhs2_) rhs2_->undo_inc_value();
        } else if (lhs_ == rhs2_) {
          if (rhs1_) rhs1_->undo_inc_value();
        } else if (rhs1_ == rhs2_) {
          if (lhs_) lhs_->undo_dec_value();
          if (rhs1_) rhs1_->undo_inc_value_twice();
        } else {
          if (lhs_) lhs_->undo_dec_value();
          if (rhs1_) rhs1_->undo_inc_value();
          if (rhs2_) rhs2_->undo_inc_value();
        }
        selected_ = false;
      } else {
        if (lhs_ == rhs1_) {
          if (rhs2_) rhs2_->undo_skip();
        } else if (lhs_ == rhs2_) {
          if (rhs1_) rhs1_->undo_skip();
        } else if (rhs1_ == rhs2_) {
          if (lhs_) lhs_->undo_skip();
        } else {
          if (lhs_) lhs_->undo_skip();
          if (rhs1_) rhs1_->undo_skip();
          if (rhs2_) rhs2_->undo_skip();
        }
      }
    }
  private:
    symbol_t* lhs_;
    symbol_t* rhs1_;
    symbol_t* rhs2_;
    bool selected_;
  };

  std::ostream& operator<<(std::ostream& o, const crule_t& rule) {
    if (rule.lhs()) {
      o << *rule.lhs() << " := ";
    } else {
      o << "nil := ";
    }
    if (rule.rhs1()) {
      o << *rule.rhs1();
    } else {
      o << "nil";
    }
    if (rule.rhs2()) {
      o << " " << *rule.rhs2();
    }
    return o;
  }

  /** Manages creation of symbols. */
  class symbol_map_t {
  public:
    typedef std::deque<symbol_t>::iterator iterator;

    /** Returns iterator pointing to first symbol added. */
    iterator begin(void) {
      return symbols_.begin();
    }

    /** Returns iterator pointing to one past the last symbol. */
    iterator end(void) {
      return symbols_.end();
    }

    /** Returns symbol associated to given state. */
    symbol_t* operator[](const state_t& state) const {
      map_t::const_iterator i = symbol_map_.find(state);
      if (i == symbol_map_.end()) sig_error("State not added");
      return i->second;
    }

    /** Adds a new nonterminal symbol associated to given state. */
    symbol_t* add(const state_t& state) {
      symbols_.push_back(symbol_t(state));
      symbol_t* result = &(symbols_.back());
      bool is_new = symbol_map_.insert(std::make_pair(state, result)).second;
      if (!is_new) throw std::logic_error("Redundant state added");
      if (!result) throw std::logic_error("Nil state found");
      return result;
    }

    /** Adds a new terminal symbol associated to given term. */
    symbol_t* add(const term_t& term) {
      symbols_.push_back(symbol_t(term));
      symbol_t* result = &(symbols_.back());
      if (!result) throw std::logic_error("Nil state found");
      return result;
    }
  private:
    typedef std::map<state_t, symbol_t*> map_t;
    /** Nonterminal and terminal symbols. */
    std::deque<symbol_t> symbols_;
    /** Maps states to symbols in the closure. */
    map_t symbol_map_;
  };

  class lcounter_t;
  typedef std::vector<symbol_t*> sym_vector_t;
  typedef std::map<sym_vector_t, std::set<const lcounter_t*> > next_map_t;

  /**
   * A state in the parse checker machine.  This needs to track the number
   * of extra tokens produced at each place (which may be negative), which
   * rules have been applied at least once, and an estimate of the number of
   * terminals read so far that is either 0, 1, or 2+.
   */
  class lcounter_t {
    friend
    std::ostream& operator<<(std::ostream& o, const lcounter_t& c);
    typedef std::set<const symbol_t*> symbol_set_t;
    typedef std::map<const symbol_t*, symbol_set_t> edge_map_t;
  public:
    /** Construct initial counter. */
    lcounter_t(const symbol_t* initial)
      : can_propagate_(initial->max_bit_flip_count() > 0) {
      carry_map_[initial] = 1;
      reachable_symbols_.insert(initial);
    }

    bool is_accepting(void) const {
      return carry_map_.empty() && (required_symbols_.size() == 0);
    }

    bool can_propagate(void) const {
      return can_propagate_;
    }

    bool operator<(const lcounter_t& c) const {
      if (carry_map_ < c.carry_map_) {
        return true;
      } else if (c.carry_map_ < carry_map_) {
        return false;
      } else if (reachable_symbols_ < c.reachable_symbols_) {
        return true;
      } else if (c.reachable_symbols_ < reachable_symbols_) {
        return false;
      } else if (required_symbols_ < c.required_symbols_) {
        return true;
      } else if (c.required_symbols_ < required_symbols_) {
        return false;
      } else {
        return edge_map_ < c.edge_map_;
      }
    }

    /**
     * Explores potential next rule selection bits given the counter.  This
     * tries selecting all combination of rules that could lead counter to
     * selected state.
     */
    void explore_next(symbol_map_t& symbols,
                      std::deque<crule_t>& rules,
                      std::set<lcounter_t>& counters,
                      std::deque<const lcounter_t*>& queue) const {
      // Initialize symbol values from carry bits.
      initialize_symbol_values(symbols.begin(), symbols.end());

      typedef std::deque<crule_t>::iterator rule_iter;
      // Points to most recently assigned rule.
      rule_iter assigned_rule = rules.end();
      bool backtracking = false;
      std::vector<term_t> terminals;
      while (!backtracking || (assigned_rule != rules.end())) {
        if (backtracking) {
          crule_t& rule = *assigned_rule;
          bool prev_selected = rule.selected();
          rule.undo_selection();
          // Backtrack
          if (prev_selected && rule.is_terminal())
            terminals.pop_back();
          if (!prev_selected && rule.try_select()) {
            if (rule.is_terminal())
              terminals.push_back(rule.lhs()->term());
            backtracking = false;
          } else {
            ++assigned_rule;
          }
        } else if (assigned_rule == rules.begin()) {
          // Consider new rule.
          lcounter_t new_counter(*this, symbols.begin(), symbols.end(),
                                 rules.begin(), rules.end());
          typedef std::set<lcounter_t>::const_iterator counter_iter;
          counter_iter ic = counters.find(new_counter);
          if (ic == counters.end()) {
            const lcounter_t* new_c
                  = &(*counters.insert(new_counter).first);
            if (new_c->can_propagate())
              queue.push_back(new_c);
          }
          backtracking = true;
        } else {
          // Select or deselect next rule.
          --assigned_rule;
          crule_t& rule = *assigned_rule;
          // First try deselecting rule.
          if (rule.try_deselect()) {
          // Next try selecting rule.
          } else if (rule.try_select()) {
            if (rule.is_terminal())
              terminals.push_back(rule.lhs()->term());
          } else {
            ++assigned_rule;
            backtracking = true;
          }
        }
      }
    }

  private:
    /**
     * Constructs a new counter from the previous one, using the counter
     * values from the symbols.
     */
    template<typename SymbolIterator, typename RuleIterator>
    lcounter_t(const lcounter_t& prev,
               const SymbolIterator& sym_begin,
               const SymbolIterator& sym_end,
               const RuleIterator& rule_begin,
               const RuleIterator& rule_end)
      : reachable_symbols_(prev.reachable_symbols_),
        required_symbols_(prev.required_symbols_),
        edge_map_(prev.edge_map_),
        can_propagate_(true) {

      // Update counter map.
      for (SymbolIterator i = sym_begin; i != sym_end; ++i) {
        const symbol_t* sym = &(*i);
        sym->check_assigned();
        if (is_odd(i->value()))
          sig_error("Sym is odd");
        carry_map_[sym] = (sym->value() / 2);
        if (!sym->can_propagate())
          can_propagate_ = false;
      }

      // Iterate through rules to add additional required_symbols and edges.
      for (RuleIterator i = rule_begin; i != rule_end; ++i) {
        const crule_t& rule = *i;
        if (rule.selected()) {
          const symbol_t* lhs = rule.lhs();
          const symbol_t* rhs1 = rule.rhs1();
          const symbol_t* rhs2 = rule.rhs2();
          if (lhs) {
            bool lhs_is_reachable = reachable_symbols_.count(lhs) > 0;
            if (lhs_is_reachable) {
              if (rhs1) add_and_close(rhs1);
              if (rhs2) add_and_close(rhs2);
            } else {
              // Add lhs to required symbols
              required_symbols_.insert(lhs);
              // Update edge map
              if (rhs1 || rhs2) {
                symbol_set_t& set = edge_map_[lhs];
                if (rhs1) set.insert(rhs1);
                if (rhs2) set.insert(rhs2);
              }
            }
          }
        }
      }
    }

    /** Initializes values in symbols. */
    template<typename SymbolIterator>
    void initialize_symbol_values(const SymbolIterator& begin,
                                  const SymbolIterator& end) const {
      carry_map_t::const_iterator imap = carry_map_.begin();
      const symbol_t* map_sym = (imap != carry_map_.end())
                              ? imap->first
                              : NULL;
      for (SymbolIterator i = begin; i != end; ++i) {
        const symbol_t* cur_sym = &(*i);
        if (map_sym == cur_sym) {
          i->initialize_next(imap->second);
          ++imap;
           map_sym = (imap != carry_map_.end())
                   ? imap->first
                   : NULL;
        } else {
          i->initialize_next(0);
        }
      }
      if (imap != carry_map_.end())
        sig_error("Did not completely read map");

    }

    /**
     * Adds symbol to reachable symbols and all symbols reachable from it.
     */
    void add_and_close(const symbol_t* sym) {
      if (reachable_symbols_.insert(sym).second) {
        typedef std::vector<const symbol_t*> queue_t;
        queue_t queue;
        queue.push_back(sym);
        required_symbols_.erase(sym);
        while (!queue.empty()) {
          const symbol_t* next = queue.back();
          queue.pop_back();
          edge_map_t::iterator iedges = edge_map_.find(next);
          if (iedges != edge_map_.end()) {
            const symbol_set_t& edge_set = iedges->second;
            typedef symbol_set_t::const_iterator set_iter;
            for (set_iter i = edge_set.begin(); i != edge_set.end(); ++i) {
              if (reachable_symbols_.insert(*i).second) {
                queue.push_back(*i);
                required_symbols_.erase(sym);
              }
            }
            edge_map_.erase(iedges);
          }
        }
      }
    }

    typedef std::map<const symbol_t*, int> carry_map_t;
    carry_map_t carry_map_;
    symbol_set_t reachable_symbols_;
    symbol_set_t required_symbols_;
    edge_map_t edge_map_;
    bool can_propagate_;
  };

  std::ostream& operator<<(std::ostream& o, const lcounter_t& c) {
    {
      o << "Non-zero counters" << std::endl;
      typedef lcounter_t::carry_map_t::const_iterator iter;
      iter iend = c.carry_map_.end();
      for (iter i = c.carry_map_.begin(); i != iend; ++i) {
        const symbol_t* sym = i->first;
        o << "  " << *sym << " = " << i->second << std::endl;
      }
    }
    return o;
  }

  template<typename Elt>
  inline void pushn(std::vector<Elt>& v, size_t count, const Elt& e) {
    v.reserve(count);
    while (count != 0) {
      v.push_back(e);
      --count;
    }
  }

  class counter_set_t {
  public:
    typedef std::set<const lcounter_t*>::const_iterator iterator;
    enum terminal_count_t { zero = 0, one = 1, two_plus = 2};

    counter_set_t()
      : prev_(NULL),
        terminal_count_(zero) {
    }

    counter_set_t(const counter_set_t* prev, const sym_vector_t& path)
      : prev_(prev),
        path_(path) {
      // Assign terminal_count_;
      switch (prev_->terminal_count_) {
      case zero:
        if (path.size() >= 2) {
          terminal_count_ = two_plus;
        } else if (path.size() == 1) {
          terminal_count_ = one;
        } else {
          terminal_count_ = zero;
        }
        break;
      case one:
        terminal_count_ = (path.size() >= 1) ? two_plus : one;
        break;
      case two_plus:
        terminal_count_ = two_plus;
        break;
      }
    }

    iterator begin(void) const {
      return set_.begin();
    }

    iterator end(void) const {
      return set_.end();
    }

    void add(const lcounter_t* c) {
      //TODO
//      // If reaching the counter used an initial rule.
//      if (c->used_initial_rule()) {
//        const boost::optional<state_t>& state = c->accepting_state();
//        // This may add a new accepting state.
//        if (state) accepting_states_.insert(*state);
//      } else {
//        // Otherwise continue exploration from this rule.
//        set_.insert(c);
//      }
    }
    template<typename Iterator>
    void add_all(const Iterator& begin, const Iterator& end) {
      for (Iterator i = begin; i != end; ++i)
        add(*i);
    }

    terminal_count_t terminal_count(void) const {
      return terminal_count_;
    }

    const std::set<state_t>& accepting_states(void) const {
      return accepting_states_;
    }

    const term_t term(const theory_t& theory, const op_t& root) const {
      size_t power = 1;
      const counter_set_t* set = this;
      std::vector<term_t> subterms;
      while (set != NULL) {
        typedef sym_vector_t::const_iterator iter;
        iter iend = set->path_.end();
        for (iter i = set->path_.begin(); i != iend; ++i)
          pushn(subterms, power, (*i)->term());
        power <<= 1;
        set = set->prev_;
      }
      return term_t(theory, root, subterms.begin(), subterms.end());
    }

    bool operator<(const counter_set_t& y) const {
      if (terminal_count_ < y.terminal_count_) {
        return true;
      } else if (terminal_count_ > y.terminal_count_) {
        return false;
      } else {
        return set_ < y.set_;
      }
    }
  private:
    /** Pointer to counter set that generated this one. */
    const counter_set_t* prev_;
    sym_vector_t path_;
    terminal_count_t terminal_count_;
    std::set<const lcounter_t*> set_;
    std::set<state_t> accepting_states_;
  };

}
  using namespace ceta::lcounter;

  class lcounter_ac_impl_t {
    typedef std::set<counter_set_t> counter_sets_t;
    typedef counter_sets_t::const_iterator set_ptr;
    typedef std::map<const lcounter_t*, next_map_t> trans_map_t;
  public:
    lcounter_ac_impl_t(const theory_t& theory,
                       const op_t& op,
                       const closure_t& closure,
                       const std::vector<rule_t>& rules)
      : theory_(theory),
        op_(op),
        axioms_(axioms(theory, op)),
        closure_(closure),
        image_(lhs_states(rules.begin(), rules.end())) {
      //std::cerr << "Hi" << std::endl;
      // Compute states appearing in rules.
      std::set<state_t> states;
      {
        closure.add_and_close_all(states,
              image_.states().begin(), image_.states().end());
        std::set<state_t> new_states
              = rhs_states(rules.begin(), rules.end());
        closure.add_and_close_all(states,
              new_states.begin(), new_states.end());
      }

      // Initialize symbols_
      {
        typedef std::set<state_t>::const_iterator iter;
        for (iter i = states.begin(); i != states.end(); ++i)
          symbols_.add(*i);
      }

      // Initialize rules_ from binary rules.
      // Note that rules are being converted from the form f(q1, q2) -> q
      // to the form q := q1 q2.  Since we talk about the left and right
      // hand sides of rules, this can be a little confusing.  state_t and
      // rule_t are referred to using the rule form f(q1, q2) -> q; crule_t
      // and symbol_t* are referred to using the rule form q := q1 q2.
      {
        typedef std::vector<rule_t>::const_iterator iter;
        for (iter i = rules.begin(); i != rules.end(); ++i) {
          const state_t& lhs1_st = lhs_state(*i, 0);
          const state_t& lhs2_st = lhs_state(*i, 1);
          const state_t& rhs_st = rhs(*i);
          // Convert rules, canceling identical states that appear on both
          // sides of rule.
          symbol_t* lhs_sym = symbols_[rhs_st];
          symbol_t* rhs_sym1 = symbols_[lhs1_st];
          symbol_t* rhs_sym2 = symbols_[lhs2_st];
          rules_.push_back(crule_t(lhs_sym, rhs_sym1, rhs_sym2));
        }
      }
      // Add epsilon rules to rules_
      { typedef std::set<state_t>::const_iterator iter;
        for (iter i = states.begin(); i != states.end(); ++i) {
          symbol_t* rhs_sym = symbols_[*i];
          const std::set<state_t>& out_edges = closure.out_edges(*i);
          for (iter j = out_edges.begin(); j != out_edges.end(); ++j) {
            symbol_t* lhs_sym = symbols_[*j];
            if (lhs_sym != rhs_sym)
              rules_.push_back(crule_t(lhs_sym, rhs_sym, NULL));
          }
        }
      }
      print_rules();


      complete_ = true;
    }

    void print_rules(void) const {
      std::cerr << "Printing rules " << std::endl;
      typedef std::deque<crule_t>::const_iterator iter;
      for (iter i = rules_.begin(); i != rules_.end(); ++i) {
        std::cerr << *i << std::endl;

      }
      std::cerr << "Done Printing rules " << std::endl;
    }

    void add_reachable(const std::set<state_t>& states, const term_t& term) {
      bool added = (kind(term) == output(op_))
                && (root(term) != op_)
                && !is_identity(root(term), axioms_)
                && image_.add(states, term);
      if (added) {
        // Get minimal states in input image.
        const std::set<state_t> nset =
              closure_.coverage_set(back(image_).first);
        // Add new symbol_
        symbol_t* new_symbol = symbols_.add(term);
        // Add new rules
        typedef std::set<state_t>::const_iterator iter;
        for (iter i = nset.begin(); i != nset.end(); ++i) {
          symbol_t* cur_sym = symbols_[*i];
          rules_.push_back(crule_t(cur_sym, new_symbol, NULL));
        }
        // Add special terminal rule.
        rules_.push_back(crule_t(new_symbol, NULL, NULL));
        complete_ = false;
      }
    }

    void explore(reachable_sets_t& reachables) {
      print_rules();
      if (complete_) return;
      // Generate initial state space
      typedef std::set<lcounter_t> counters_t;

      counters_t counters;
      trans_map_t trans_map;
      // Initialize counters and trans_map
      {
        std::deque<const lcounter_t*> queue;

        typedef symbol_map_t::iterator sym_iter;
        for (sym_iter i = symbols_.begin(); i != symbols_.end(); ++i) {
          const lcounter_t* new_counter
              = &(*counters.insert(lcounter_t(&(*i))).first);
          queue.push_back(new_counter);
        }
        while (!queue.empty()) {
          const lcounter_t* c = queue.front();
          queue.pop_front();
          c->explore_next(symbols_, rules_, counters, queue);
        }
      }
//      { // Perform subset construction
//        counter_sets_t counter_sets;
//        counter_set_t initial_set;
//        initial_set.add(initial_counter);
//        set_ptr i = counter_sets.insert(initial_set).first;
//        std::deque<set_ptr> queue;
//        queue.push_back(i);
//        while (!queue.empty()) {
//          std::cerr << "Subset contruction: set_size: "
//                    << counter_sets.size()
//                    << " queue_size: " << queue.size() << std::endl;
//          const counter_set_t* set = &(*(queue.front()));
//          explore_next(counter_sets, queue, trans_map, set, reachables);
//          queue.pop_front();
//        }
//      }
      complete_ = true;
    }

    bool is_complete(void) const {
      return complete_;
    }
  private:
    void explore_next(counter_sets_t& counter_sets,
                      std::deque<set_ptr>& queue,
                      const trans_map_t& trans_map,
                      const counter_set_t* set,
                      reachable_sets_t& reachables) {
      typedef std::map<sym_vector_t, counter_set_t> next_counter_map_t;
      next_counter_map_t next_counter_map;
      // Add reachable states to next_counter_map
      {
        typedef counter_set_t::iterator iter;
        for (iter i = set->begin(); i != set->end(); ++i) {
          const next_map_t& nmap = trans_map.find(*i)->second;
          typedef next_map_t::const_iterator iter;
          for (iter j = nmap.begin(); j != nmap.end(); ++j) {
            const sym_vector_t& terminals = j->first;
            next_counter_map_t::iterator im =
                    next_counter_map.find(terminals);
            if (im == next_counter_map.end()) {
              im = next_counter_map.insert(std::make_pair(terminals,
                    counter_set_t(set, terminals))).first;
            }
            im->second.add_all(j->second.begin(), j->second.end());
          }
        }
      }
      // Add new counter_sets and reachables.
      {
        typedef next_counter_map_t::iterator iter;
        iter iend = next_counter_map.end();
        for (iter i = next_counter_map.begin(); i != iend; ++i) {
          const counter_set_t& next_set = i->second;

          if ((next_set.terminal_count() == counter_set_t::two_plus)
              && !reachables.contains(next_set.accepting_states(), op_)) {
            reachables.add(next_set.accepting_states(),
                           next_set.term(theory_, op_));
          }
          typedef std::pair<set_ptr, bool> insert_result_t;
          insert_result_t result = counter_sets.insert(next_set);
          // Add to queue if next_set is new
          if (result.second)
            queue.push_back(result.first);
        }
      }
    }

    theory_t theory_;
    op_t op_;
    axiom_set_t axioms_;
    const closure_t& closure_;
    /** Reachable states that are terminals in the explorer. */
    reachable_image_t image_;
    symbol_map_t symbols_;

    std::deque<crule_t> rules_;
    bool complete_;

  };

  lcounter_ac_explorer_t::lcounter_ac_explorer_t(
          const theory_t& theory,
          const op_t& op,
          const closure_t& closure,
          const std::vector<rule_t>& rules)
    : impl_(new lcounter_ac_impl_t(theory, op, closure, rules)) {
  }

  void lcounter_ac_explorer_t::add_reachable(
          const std::set<state_t>& states, const term_t& term) {
    impl_->add_reachable(states, term);
  }

  void lcounter_ac_explorer_t::explore(reachable_sets_t& reachables) {
    impl_->explore(reachables);
  }

  bool lcounter_ac_explorer_t::is_complete(void) const {
    return impl_->is_complete();
  }
}
