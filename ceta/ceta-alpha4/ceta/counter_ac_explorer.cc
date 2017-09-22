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

#include "counter_ac_explorer.hh"
#include <iostream>

#include "reachable_image.hh"
#include "trans_closure.hh"

namespace ceta {
namespace counter {
  void sig_error(const std::string& s) NO_RETURN;
  void sig_error(const std::string& s) {
    int* x = 0;
    *x = 123;
    throw std::logic_error(s);
  }


  class crule_t;

  /**
   * A nonterminal or terminal symbol in CFG.
   * Invariants:
   *  min_potential <= value <= max_potential
   *  max_potential >= min_allowed_value
   *  min_potential <= max_allowed_value
   *  min_allowed_value = min(-(rhs_sum_ - 1), 0)
   *  max_allowed_value = max(lhs_sum_ - 1, 0)
   *  lhs_sum_ = # of occurences of symbol in lhs production rule "s := w"
   *  rhs_sum_ = # of occurences of symbol in rhs of production rule "s := w"
   */
  class symbol_t {
  public:
    template<typename Data>
    explicit symbol_t(const Data& data)
      : data_(data),
        lhs_sum_(0),
        rhs_sum_(0),
        value_(0),
        min_potential_(0),
        max_potential_(0) {
      check_invariants();
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

    /**
     * Initializes symbol for use with next instance. We assume
     * min_allowed_value <= prev_value <= max_allowed_value.
     */
    void initialize_next(int prev_value) {
      if ((min_allowed_value() > prev_value)
       || (max_allowed_value() < prev_value)) {
        throw std::logic_error("Illegal previous value");
      }
      // Compute number of occurences on left hand side and rhs of rules.
      value_ = 2 * prev_value;
      min_potential_ = value_ - lhs_sum_;
      max_potential_ = value_ + rhs_sum_;
      check_invariants();
    }

    bool can_inc_min_potential(void) const {
      return min_potential_ < max_allowed_value();
    }

    void inc_min_potential(void) {
      ++min_potential_;
      check_invariants();
    }

    void undo_inc_min_potential(void) {
      --min_potential_;
      check_invariants();
    }

    bool can_dec_max_potential(void) const {
     return max_potential_ > min_allowed_value();
    }

    bool can_dec_max_potential_twice(void) const {
     return max_potential_ - 2 >= min_allowed_value();
    }

    void dec_max_potential(void) {
      --max_potential_;
      check_invariants();
    }

    bool try_dec_max_potential(void) {
      bool result = can_dec_max_potential();
      if (result) dec_max_potential();
      return result;
    }


    void undo_dec_max_potential(void) {
      ++max_potential_;
      check_invariants();
    }

    int value(void) const {
      return value_;
    }

    bool can_dec_value(void) const {
      return can_dec_max_potential();
    }

    void dec_value(void) {
      --value_;
      --max_potential_;
      check_invariants();
    }

    void undo_dec_value(void) {
      ++value_;
      ++max_potential_;
      check_invariants();
    }

    bool can_inc_value(void) const {
      return can_inc_min_potential();
    }

    bool can_inc_value_twice(void) const {
      return (min_potential_ + 2 <= max_allowed_value());
    }

    void inc_value(void) {
      ++value_;
      ++min_potential_;
      check_invariants();
    }

    bool try_inc_value(void) {
      bool result = can_inc_value();
      if (result) inc_value();
      return result;
    }

    void undo_inc_value(void) {
      --value_;
      --min_potential_;
      check_invariants();
    }

    int min_allowed_value(void) const {
      return (rhs_sum_ == 0) ? 0 : -(rhs_sum_ - 1);
    }
    int max_allowed_value(void) const {
      return (lhs_sum_ == 0) ? 0 : lhs_sum_ - 1;
    }

    void check_assigned(void) const {
      if (min_potential_ != value_)
        sig_error("Min potential incorrect");
      if (value_ != max_potential_)
        sig_error("Max potential incorrect");
      if (value_ < min_allowed_value())
        sig_error("Value too low");
      if (value_ > max_allowed_value())
        sig_error("Value too high");
      check_invariants();
    }

    void inc_lhs_sum(void) {
      ++lhs_sum_;
    }
    void inc_rhs_sum(void) {
      ++rhs_sum_;
    }
  private:
    void check_invariants(void) const {
      if (value_ - lhs_sum_ > min_potential_)
        sig_error("Min potential too low");
      if (min_potential_ > value_)
        sig_error("Min potential too high");
      if (value_ > max_potential_)
        sig_error("Max potential too low");
      if (max_potential_ > value_ + rhs_sum_)
        sig_error("Max potential too high");
      if (max_potential_ < min_allowed_value())
        sig_error("Max potential out of range");
      if (min_potential_ > max_allowed_value())
        sig_error("Min potential out of range");
    }
    boost::variant<state_t, term_t> data_;
    /** Number of times symbol appears in lhs of a rule. */
    int lhs_sum_;
    /** Number of times symbol appears in rhs of a rule. */
    int rhs_sum_;
    /** Times symbol is created minus times symbol is consumed. */
    int value_;
    /** Minimum potential value of symbol. */
    int min_potential_;
    /** Maximum potential value of symbol. */
    int max_potential_;
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
        if (rhs2) rhs2->inc_rhs_sum();
      } else if (lhs == rhs2) {
        // If lhs != rhs1 /\ lhs == rhs2
        if (rhs1) rhs1->inc_rhs_sum();
      } else {
        if (lhs) lhs->inc_lhs_sum();
        if (rhs1) rhs1->inc_rhs_sum();
        if (rhs2) rhs2->inc_rhs_sum();
      }
    }

    /** Returns true if this rule is of the form terminal := nil. */
    bool is_terminal(void) const {
      return lhs_ && lhs_->is_terminal();
    }

    /**
     * Returns true if this is an "initial" rule that creates the first
     * nonterminal.
     */
    bool is_initial(void) const {
      return lhs_ == NULL;
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
        result = !rhs2_ || rhs2_->try_inc_value();
      } else if (lhs_ == rhs2_) {
        result = !rhs1_ || rhs1_->try_inc_value();
      } else if (rhs1_ == rhs2_) {
        result = (!lhs_ || lhs_->can_dec_value())
              && (!rhs1_ || rhs1_->can_inc_value_twice());
        if (result) {
          if (lhs_) lhs_->dec_value();
          if (rhs1_) {
            rhs1_->inc_value();
            rhs1_->inc_value();
          }
        }
      } else { // All three symbols distinct
        result = (!lhs_ || lhs_->can_dec_value())
              && (!rhs1_ || rhs1_->can_inc_value())
              && (!rhs2_ || rhs2_->can_inc_value());
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
        result = !rhs2_ || rhs2_->try_dec_max_potential();
      } else if (lhs_ == rhs2_) {
        result = !rhs1_ || rhs1_->try_dec_max_potential();
      } else if (rhs1_ == rhs2_) {
        result = (!lhs_ || lhs_->can_inc_min_potential())
              && (!rhs1_ || rhs1_->can_dec_max_potential_twice());
        if (result) {
          if (lhs_) lhs_->inc_min_potential();
          if (rhs1_) {
            rhs1_->dec_max_potential();
            rhs1_->dec_max_potential();
          }
        }
      } else { // All three symbols distinct
        result = (!lhs_ || lhs_->can_inc_min_potential())
              && (!rhs1_ || rhs1_->can_dec_max_potential())
              && (!rhs2_ || rhs2_->can_dec_max_potential());
        if (result) {
          if (lhs_) lhs_->inc_min_potential();
          if (rhs1_) rhs1_->dec_max_potential();
          if (rhs2_) rhs2_->dec_max_potential();
        }
      }
      if (result) selected_ = false;
      return result;
    }


    /** Undo last selection action. */
    void undo_selection(void) {
      if (selected_) {
        if (lhs_ == rhs1_) {
          if (rhs2_) rhs2_->undo_inc_value();
        } else if (lhs_ == rhs2_) {
          if (rhs1_) rhs1_->undo_inc_value();
        } else {
          if (lhs_) lhs_->undo_dec_value();
          if (rhs1_) rhs1_->undo_inc_value();
          if (rhs2_) rhs2_->undo_inc_value();
        }
        selected_ = false;
      } else {
        if (lhs_ == rhs1_) {
          if (rhs2_) rhs2_->undo_dec_max_potential();
        } else if (lhs_ == rhs2_) {
          if (rhs1_) rhs1_->undo_dec_max_potential();
        } else {
          if (lhs_) lhs_->undo_inc_min_potential();
          if (rhs1_) rhs1_->undo_dec_max_potential();
          if (rhs2_) rhs2_->undo_dec_max_potential();
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

  class counter_t;
  typedef std::vector<term_t> term_vector_t;
  typedef std::vector<const symbol_t*> sym_vector_t;
  typedef std::map<sym_vector_t, std::set<const counter_t*> > next_map_t;

  /**
   * A state in the parse checker machine.  This needs to track the number
   * of extra tokens produced at each place (which may be negative), which
   * rules have been applied at least once, and an estimate of the number of
   * terminals read so far that is either 0, 1, or 2+.
   */
  class counter_t {
    friend
    std::ostream& operator<<(std::ostream& o, const counter_t& c);
    typedef std::set<const symbol_t*> symbol_set_t;
    typedef std::map<const symbol_t*, symbol_set_t> edge_map_t;
  public:
    /** Construct initial counter. */
    counter_t(void) {
    }

    bool used_initial_rule(void) const {
      return used_initial_rule_;
    }

    /** Returns state used in initial rule if any. */
    const boost::optional<state_t>& accepting_state(void) const {
      return accepting_state_;
    }

    bool operator<(const counter_t& c) const {
      if (counter_map_ < c.counter_map_) {
        return true;
      } else if (c.counter_map_ < counter_map_) {
        return false;
      } else if (required_symbols_ < c.required_symbols_) {
        return true;
      } else if (c.required_symbols_ < required_symbols_) {
        return false;
      } else {
        return (reachable_map_ < c.reachable_map_);
      }
    }

    /**
     * Explores potential next rule selection bits given the counter.  This
     * tries selecting all combination of rules that could lead counter to
     * selected state.
     */
    void explore_next(symbol_map_t& symbols,
                      std::deque<crule_t>& rules,
                      std::set<counter_t>& counters,
                      std::deque<const counter_t*>& queue,
                      next_map_t& next_map) const {
      // Initialize symbol values from counter.
      initialize_symbol_values(symbols.begin(), symbols.end());
      bool initial_rule_selected = false;
      typedef std::deque<crule_t>::iterator rule_iter;
      // Points to most recently assigned rule.
      rule_iter assigned_rule = rules.end();
      bool backtracking = false;
      sym_vector_t terminals;
      while (!backtracking || (assigned_rule != rules.end())) {
        if (backtracking) {
          crule_t& rule = *assigned_rule;
          bool prev_selected = rule.selected();
          rule.undo_selection();
          // Backtrack
          if (prev_selected && rule.is_initial())
            initial_rule_selected = false;
          if (prev_selected && rule.is_terminal())
            terminals.pop_back();
          bool can_try = !prev_selected
                      && !(initial_rule_selected && rule.is_initial());
          if (can_try && rule.try_select()) {
            if (rule.is_initial()) initial_rule_selected = true;
            if (rule.is_terminal())
              terminals.push_back(rule.lhs());
            backtracking = false;
          } else {
            ++assigned_rule;
          }
        } else if (assigned_rule == rules.begin()) {
          counter_t new_counter(*this, symbols.begin(), symbols.end(),
                                rules.begin(), rules.end());
          const counter_t* new_c;
          // Get pointer to counter in counters.
          {
            typedef std::set<counter_t>::const_iterator counter_iter;
            counter_iter ic = counters.find(new_counter);
            if (ic == counters.end()) {
              new_c = &(*counters.insert(new_counter).first);
              if (!new_c->used_initial_rule())
                queue.push_back(new_c);
            } else {
              new_c = &(*ic);
            }
          }
          next_map[terminals].insert(new_c);
          backtracking = true;
        } else {
          // Select or deselect next rule.
          --assigned_rule;
          crule_t& rule = *assigned_rule;
          // First try deselecting rule.
          if (rule.try_deselect()) {
          // Next try selecting rule.
          } else if (!(initial_rule_selected && rule.is_initial())
              && rule.try_select()) {
            if (rule.is_initial()) initial_rule_selected = true;
            if (rule.is_terminal())
              terminals.push_back(rule.lhs());
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
    counter_t(const counter_t& prev,
               const SymbolIterator& sym_begin, const SymbolIterator& sym_end,
               const RuleIterator& rule_begin, const RuleIterator& rule_end)
      : edge_map_(prev.edge_map_),
        required_symbols_(prev.required_symbols_),
        used_initial_rule_(false) {

      // Update counter map.
      for (SymbolIterator i = sym_begin; i != sym_end; ++i) {
        const symbol_t* sym = &(*i);
        sym->check_assigned();
        if (i->value() != 0)
          counter_map_[sym] = sym->value();
      }

      const symbol_t* initial_symbol = NULL;

      // Iterate through used rules to initial data structures.
      for (RuleIterator i = rule_begin; i != rule_end; ++i) {
        const crule_t& rule = *i;
        if (!rule.selected())
          continue;
        const symbol_t* lhs = rule.lhs();
        const symbol_t* rhs1 = rule.rhs1();
        const symbol_t* rhs2 = rule.rhs2();
        if (lhs) {
          // Update edge map
          if (rhs1 || rhs2) {
            symbol_set_t& set = edge_map_[lhs];
            if (rhs1) set.insert(rhs1);
            if (rhs2) set.insert(rhs2);
          }
          required_symbols_.insert(lhs);
        }
        // Set initial_symbol if rule is initial.
        if (rule.is_initial()) {
          if (used_initial_rule_)
            throw std::logic_error("Already added initial rule.");
          used_initial_rule_ = true;
          initial_symbol = rhs1;
        }
      }

      for (SymbolIterator i = sym_begin; i != sym_end; ++i) {
        const symbol_t* sym = &(*i);
        symbol_set_t& set = reachable_map_[sym];
        add_and_close(edge_map_, set, sym);
      }

      // An initial state is accepting if all counter values are zero and
      // every negative state is reachable.
      if (counter_map_.empty() && used_initial_rule_) {
        symbol_set_t reachable_symbols = reachable_map_[initial_symbol];
        typedef symbol_set_t::const_iterator iter;
        iter ibegin = required_symbols_.begin();
        iter iend = required_symbols_.end();
        bool accepting = true;
        for (iter i = ibegin; accepting && i != iend; ++i)
          accepting = (reachable_symbols.count(*i) > 0);
        if (accepting)
          accepting_state_ = initial_symbol->state();
      }
    }

    /** Initializes values in symbols. */
    template<typename SymbolIterator>
    void initialize_symbol_values(const SymbolIterator& begin,
                                  const SymbolIterator& end) const {
      for (SymbolIterator i = begin; i != end; ++i) {
        const symbol_t* cur_sym = &(*i);
        counter_map_t::const_iterator imap = counter_map_.find(cur_sym);
        if (imap != counter_map_.end()) {
          i->initialize_next(imap->second);
        } else {
          i->initialize_next(0);
        }
      }
    }

    typedef std::map<const symbol_t*, int> counter_map_t;
    typedef std::set<const crule_t*> used_rules_t;
    typedef std::map<const symbol_t*, symbol_set_t> reachable_map_t;
    counter_map_t counter_map_;
    edge_map_t edge_map_;
    symbol_set_t required_symbols_;
    reachable_map_t reachable_map_;
    used_rules_t used_rules_;
    bool used_initial_rule_;
    boost::optional<state_t> accepting_state_;
  };

  std::ostream& operator<<(std::ostream& o, const counter_t& c) {
    {
      o << "Non-zero counters" << std::endl;
      typedef counter_t::counter_map_t::const_iterator iter;
      iter iend = c.counter_map_.end();
      for (iter i = c.counter_map_.begin(); i != iend; ++i) {
        const symbol_t* sym = i->first;
        o << "  " << *sym << " = " << i->second
          << " min: " << sym->min_allowed_value()
          << " max: " << sym->max_allowed_value()
          << std::endl;

        if ((sym->min_allowed_value() > i->second)
         || (sym->max_allowed_value() < i->second)) {
          sig_error("Fool");
        }
      }
    }
    {
      o << "Used rules" << std::endl;
      typedef counter_t::used_rules_t::const_iterator iter;
      iter iend = c.used_rules_.end();
      for (iter i = c.used_rules_.begin(); i != iend; ++i) {
        o << "  " << **i << std::endl;
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
    typedef std::set<const counter_t*>::const_iterator iterator;
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

    void add(const counter_t* c) {
      // If reaching the counter used an initial rule.
      if (c->used_initial_rule()) {
        const boost::optional<state_t>& state = c->accepting_state();
        // This may add a new accepting state.
        if (state) accepting_states_.insert(*state);
      } else {
        // Otherwise continue exploration from this rule.
        set_.insert(c);
      }
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
    std::set<const counter_t*> set_;
    std::set<state_t> accepting_states_;
  };

}
  using namespace ceta::counter;

  class counter_ac_impl_t {
    typedef std::set<counter_set_t> counter_sets_t;
    typedef counter_sets_t::const_iterator set_ptr;
    typedef std::map<const counter_t*, next_map_t> trans_map_t;
  public:
    counter_ac_impl_t(const theory_t& theory,
                      const op_t& op,
                      const closure_t& closure,
                      const std::vector<rule_t>& rules)
      : theory_(theory),
        op_(op),
        axioms_(axioms(theory, op)),
        closure_(closure),
        image_(lhs_states(rules.begin(), rules.end())) {
      // Compute states appearing in rules.
      std::set<state_t> states;
      {
        std::set<state_t> lhs_state_set
              = lhs_states(rules.begin(), rules.end());
        closure.add_and_close_all(states,
              lhs_state_set.begin(), lhs_state_set.end());
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
          const std::set<state_t>& out_edges = closure.out_edges(*i);
          for (iter j = out_edges.begin(); j != out_edges.end(); ++j) {
            symbol_t* lhs_sym = symbols_[*j];
            symbol_t* rhs_sym = symbols_[*i];
            rules_.push_back(crule_t(lhs_sym, rhs_sym, NULL));
          }
        }
      }

      // Add initial production rule for each symbol.
      // These are added last because that may be more efficient.
      {
        typedef std::set<state_t>::const_iterator iter;
        for (iter i = states.begin(); i != states.end(); ++i) {
          rules_.push_back(crule_t(NULL, symbols_[*i], NULL));
        }
      }
      complete_ = true;
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
      if (complete_) return;
      // Generate initial state space
      typedef std::set<counter_t> counters_t;

      counters_t counters;
      trans_map_t trans_map;
      const counter_t* initial_counter
              = &(*counters.insert(counter_t()).first);
      // Initialize counters and trans_map
      { // Initially run -- explored_count: 11839 min_count: 128
        // Revised run -- explored_count: 640
        std::deque<const counter_t*> queue;
        queue.push_back(initial_counter);
        while (!queue.empty()) {
          const counter_t* c = queue.front();
          queue.pop_front();
          next_map_t& next_map = trans_map.insert(
                  std::make_pair(c, next_map_t())).first->second;
          c->explore_next(symbols_, rules_, counters, queue, next_map);
        }
      }
      { // Perform subset construction
        counter_sets_t counter_sets;
        counter_set_t initial_set;
        initial_set.add(initial_counter);
        set_ptr i = counter_sets.insert(initial_set).first;
        std::deque<set_ptr> queue;
        queue.push_back(i);
        while (!queue.empty()) {
          const counter_set_t* set = &(*(queue.front()));
          explore_next(counter_sets, queue, trans_map, set, reachables);
          queue.pop_front();
        }
      }
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

  counter_ac_explorer_t::counter_ac_explorer_t(
          const theory_t& theory,
          const op_t& op,
          const closure_t& closure,
          const std::vector<rule_t>& rules)
    : impl_(new counter_ac_impl_t(theory, op, closure, rules)) {
  }

  void counter_ac_explorer_t::add_reachable(
          const std::set<state_t>& states, const term_t& term) {
    impl_->add_reachable(states, term);
  }

  void counter_ac_explorer_t::explore(reachable_sets_t& reachables) {
    impl_->explore(reachables);
  }

  bool counter_ac_explorer_t::is_complete(void) const {
    return impl_->is_complete();
  }
}
