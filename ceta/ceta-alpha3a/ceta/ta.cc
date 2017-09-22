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
/**
 * \file
 * Implementation for propositional tree automata operations.
 */
#include "ta.hh"
#include "writer.hh"

#include <list>
#include <map>
#include <stdexcept>

using namespace std;

namespace ceta {
  namespace impl {
    /**
     * Signal that a logical error occurred in the execution of the program
     * by printing an error message and segfaulting.
     */
    static void sig_error(const std::string& msg) NO_RETURN;

    static void sig_error(const std::string& msg) {
      throw std::logic_error(msg);
    }

    /**
     * Returns true if distance(first1, last1) == distance(first2, last2) and
     * elements in range [first1 ... last1) and [first2 ... last2) are
     * identical.
     */
    template<typename I1, typename I2>
    static
    bool equal(I1 first1, I1 last1, I2 first2, I2 last2) {
      while ((first1 != last1) && (first2 != last2)) {
        if (*first1 != *first2)
          return false;
        ++first1;
        ++first2;
      }
      // Check that both iterators reached end of list.
      return (first1 == last1) && (first2 == last2);
    }

    /**
     * Returns true if iterators point to ranges of equal length and
     * predicated is true for each consequentify pair of elements in the
     * ranges.
     */
    template<typename I1, typename I2, typename P>
    static
    bool equal(I1 first1, I1 last1, I2 first2, I2 last2, P predicate) {
      while ((first1 != last1) && (first2 != last2)) {
        if (!predicate(*first1, *first2))
          return false;
        ++first1;
        ++first2;
      }
      // Check that both iterators reached end of list.
      return (first1 == last1) && (first2 == last2);
    }

    /** Clones pointer if necessary to insure this is not shared. */
    template<typename T>
    static
    void make_unique(boost::shared_ptr<T>& ptr) {
      if (!ptr.unique())
        ptr = boost::shared_ptr<T>(new T(*ptr));
    }

    /**
     * Checks that operator is binary.
     * \relates op_t
     */
    static
    void check_binary(const op_t& op) {
      if (!is_binary(op))
        sig_error(name(op) + " is not a binary operator.");
    }

    /**
     * Checks that element is in theory.
     * \relates theory_t
     */
    template<typename E>
    static
    void check_member(const theory_t& theory, const E& elt) {
      if (!member(theory, elt))
        sig_error(name(elt) + " is not in theory.");
    }

    /** Checks that two theories are equal. */
    static
    void check_equal(const theory_t& x, const theory_t& y) {
      if (x != y)
        sig_error("Theories are not equal.");
    }

    /**
     * An adaptable binary predicate that returns true if the two ops it is
     * passed are equal and have the same equational axioms in each theory.
     */
    class ops_equivalent {
    public:
      /** Constructs ops_equivalent predicate for two theories. */
      ops_equivalent(const theory_t& lhs, const theory_t& rhs)
        : lhs_(lhs), rhs_(rhs) {
      }
      /**
       * Returns true if ops are equivalent with respect to the two theories.
       */
      bool operator()(const op_t& x, const op_t& y) const {
        return (x == y) && (axioms(lhs_, x) == axioms(rhs_, y));
      }
    private:
      /** Theory to examine first op in. */
      theory_t lhs_;
      /** Theory to examine second op in. */
      theory_t rhs_;
    };

    /**
     * A finite parameterized automorphism class.  An automorphism is a
     * function whose domain and range are equivalent.  In this case, the
     * automophism only maps a finite number of objects to something other
     * than themselves.
     */
    template<typename Element>
    class automorphism_t {
    public:
      /** Type of constant bidirectional iterator over pairs of elements. */
      typedef typename std::map<Element, Element>::const_iterator iterator;
      typedef std::pair<Element, Element> pair_type;

      iterator begin() const {
        return mapping_.begin();
      }

      iterator end() const {
        return mapping_.end();
      }

      /** Returns value of e in morphism. */
      const Element& operator()(const Element& e) const {
        iterator i = mapping_.find(e);
        if (i != mapping_.end()) {
          return i->second;
        } else {
          return e;
        }
      }

      template<typename Other>
      const Other operator()(const Other& other) const {
        return apply(*this, other);
      }

      void set(const Element& e, const Element& v) {
        mapping_.insert(make_pair(e, v));
      }
    private:
      map<Element, Element> mapping_;
    };

    typedef automorphism_t<state_t> state_subst_t;

    /**
     * Constructs a state substitution that renames states appearing in both
     * automata to fresh states.
     */
    const state_subst_t make_state_subst(const ta_t& x, const ta_t& y) {
      state_subst_t result;
      typedef ta_t::state_iterator iter;
      iter i = states_begin(x);
      iter j = states_begin(y);
      while ((i != states_end(x)) && (j != states_end(y))) {
        if (*i < *j) {
          ++i;
        } else if (*j < *i) {
          ++j;
        } else { // Same state appears in states for x and y.
          // Bind state to fresh state with same kind.
          state_t state = *i;
          state_t new_state(kind(state), name(state) + "'");
          result.set(state, new_state);
          ++i;
          ++j;
        }
      }
      return result;
    }

    /**
     * Visitor to state predicates that checks if set is a model of predicate
     * this is visiting.  There is a separate <code>operator()</code>
     * function for each type of predicate.
     */
    class predicate_models_visitor {
    public:
      typedef bool result_type;
      /** Constructs visitor that checks predicates using model. */
      predicate_models_visitor(const std::set<state_t>& model)
        : model_(model) {
      }
      bool operator()(bool value) const {
        return value;
      }
      bool operator()(const state_t& state) const {
        return model_.count(state) > 0;
      }
      bool operator()(const not_predicate_t& pred) const {
        return !apply_visitor(*this, pred.arg);
      }
      bool operator()(const and_predicate_t& pred) const {
        return apply_visitor(*this, pred.lhs)
            && apply_visitor(*this, pred.rhs);
      }
      bool operator()(const or_predicate_t& pred) const {
        return apply_visitor(*this, pred.lhs)
            || apply_visitor(*this, pred.rhs);
      }
    private:
      const set<state_t>& model_;
    };

    /** Enumeration giving operator priorities in predicate. */
    enum priority_t
            { OR_PRIORITY = 1, AND_PRIORITY = 2, TOP_PRIORITY = 3 };

    /**
     * Visitor to state predicates that returns priority of top operator of
     * predicate.
     */
    struct priority_visitor {
      typedef priority_t result_type;

      template<typename T>
      priority_t operator()(const T&) const {
        return TOP_PRIORITY;
      }
      priority_t operator()(const and_predicate_t&) const {
        return AND_PRIORITY;
      }
      priority_t operator()(const or_predicate_t&) const {
        return OR_PRIORITY;
      }
    };
    /** Returns priority of top operator of predicate. */
    static
    priority_t priority(const state_predicate_t& pred) {
      return apply_visitor(priority_visitor(), pred);
    }

    /** Visitor to state predicate that writes it to ostream. */
    class print_visitor {
    public:
      typedef void result_type;
      /** Constructs vistor that writes to given output stream. */
      print_visitor(ostream& o)
        : o_(o) {
      }
      void operator()(bool value) const {
        o_ << (value ? "true" : "false");
      }
      void operator()(const state_t& state) const {
        o_ << state;
      }
      void operator()(const not_predicate_t& pred) const {
        o_ << "!";
        print(pred.arg, TOP_PRIORITY);
      }
      void operator()(const and_predicate_t& pred) const {
        print(pred.lhs, AND_PRIORITY);
        o_ << " & ";
        print(pred.rhs, AND_PRIORITY);
      }
      void operator()(const or_predicate_t& pred) const {
        print(pred.lhs, OR_PRIORITY);
        o_ << " | ";
        print(pred.rhs, OR_PRIORITY);
      }
    private:
      /**
       * Prints state predicate surrounded by parenthesis if needed based
       * on operator priority.
       */
      void print(const state_predicate_t& pred,
                 priority_t parent_priority) const {
        // Print parenthesis if predicate's priority is lower than parent's.
        bool print_parens = priority(pred) < parent_priority;
        if (print_parens) o_ << "(";
        apply_visitor(*this, pred);
        if (print_parens) o_ << ")";
      }
      ostream& o_;
    };

    /** Check that a state is a member of automaton. */
    static
    void check_member(const ta_t& ta, const state_t& state) {
      if (!member(ta, state))
        sig_error("State " + name(state) + " is not a member of automaton.");
    }

    /**
     * Visitor to state predicates that checks if each state in predicate is
     * in the automaton.
     */
    struct check_state_visitor {
      typedef void result_type;
      /** Construct visitor that checks predicates using automaton. */
      explicit check_state_visitor(const ta_t& ta)
        : ta_(ta) {
      }
      void operator()(bool value) const {
      }
      void operator()(const state_t& state) const {
        check_member(ta_, state);
      }
      void operator()(const not_predicate_t& pred) const {
        apply_visitor(*this, pred.arg);
      }
      void operator()(const and_predicate_t& pred) const {
        apply_visitor(*this, pred.lhs);
        apply_visitor(*this, pred.rhs);
      }
      void operator()(const or_predicate_t& pred) const {
        apply_visitor(*this, pred.lhs);
        apply_visitor(*this, pred.rhs);
      }
    private:
      const ta_t ta_;
    };

    /** Checks that each state in predicate is in tree automaton. */
    static
    void check_states(const ta_t& ta, const state_predicate_t& pred) {
      apply_visitor(check_state_visitor(ta), pred);
    }

    /**
     * Visitor to state predicates that renames states in predicate using
     * substitution.
     */
    struct rename_visitor {
      typedef const state_predicate_t result_type;

      rename_visitor(const kind_t& kind, const state_subst_t& subst)
        : kind_(kind), subst_(subst) {
      }
      state_predicate_t operator()(bool value) const {
        return state_predicate_t(kind_, value);
      }
      state_predicate_t operator()(const state_t& state) const {
        return state_predicate_t(subst_(state));
      }
      state_predicate_t operator()(const not_predicate_t& pred) const {
        return ! apply_visitor(*this, pred.arg);
      }
      state_predicate_t operator()(const and_predicate_t& pred) const {
        return apply_visitor(*this, pred.lhs)
             & apply_visitor(*this, pred.rhs);
      }
      state_predicate_t operator()(const or_predicate_t& pred) const {
        return apply_visitor(*this, pred.lhs)
             | apply_visitor(*this, pred.rhs);
      }
    private:
      const kind_t kind_;
      const state_subst_t& subst_;
    };

    /**
     * Returns a copy of a state predicate in which each state has been
     * changed using the substitution.
     */
    static
    const state_predicate_t apply(const state_subst_t& subst,
                                  const state_predicate_t& pred) {
      return apply_visitor(rename_visitor(kind(pred), subst), pred);
    }

    /** Mapping from operator to axiom set. */
    typedef map<op_t, axiom_set_t> axiom_map_t;
    /**
     * Unary function which writes a declaration of its argument to the
     * provided output stream.
     */
    class decl_writer {
    public:
      typedef void result_type;

      /** Constructs a decl_writer that writes declarations to o. */
      decl_writer(ostream* o, const theory_t* theory)
        : o_(o),
          theory_(theory) {
      }

      /** Writes kind declararation. */
      void operator()(const kind_t& kind) {
        *o_ << "kind " << name(kind) << ";" << endl;
      }

      /** Writes operator declaration. */
      void operator()(const op_t& op) {
        *o_ << "op " << name(op) << " : "
            << make_range_writer(inputs_begin(op), inputs_end(op))
            << " -> " << output(op)
            << " [" << axioms(*theory_, op) << "];" << endl;
      }
      void operator()(const state_t& state) {
        *o_ << "state " << name(state)
            << " -> " << kind(state) << ";" << endl;
      }
      void operator()(const state_predicate_t& pred) {
        *o_ << "accept " << kind(pred) << " : " << pred << ";" << endl;
      }
      void operator()(const erule_t& erule) {
        *o_ << "rl " << lhs(erule) << " -> " << rhs(erule) << ";" << endl;
      }
      void operator()(const rule_t& rule) {
        *o_ << "rl " << op(rule);
        if (lhs_states_begin(rule) != lhs_states_end(rule)) {
          *o_ << "("
              << make_range_writer(lhs_states_begin(rule),
                                   lhs_states_end(rule),
                                   ", ")
              << ")";
        }
        *o_ << " -> " << rhs(rule) << ";" << endl;
      }
    private:
      ostream* o_;
      const theory_t* theory_;
    };

    /**
     * Creates new erule by applying substitution to lhs and rhs of existing
     * erule.
     */
    static
    const erule_t apply(const state_subst_t& subst, const erule_t& erule) {
      return erule_t(subst(lhs(erule)), subst(rhs(erule)));
    }

    static
    const rule_t apply(const state_subst_t& subst, const rule_t& rule) {
      // Create vector of renamed states
      std::vector<state_t> lhs;
      lhs.reserve(lhs_state_count(rule));
      // Add renamed states to vector
      typedef rule_t::lhs_state_iterator iter;
      for (iter i = lhs_states_begin(rule); i != lhs_states_end(rule); ++i)
        lhs.push_back(subst(*i));
      // Return new rule
      return rule_t(op(rule), lhs.begin(), lhs.end(), subst(rhs(rule)));
    }

    /** For each iterator i in [start end), adds fn(i) to ta. */
    template<typename I, typename AddFn, typename Fn>
    static void add_range(I start, I end, AddFn add_fn, ta_t& ta, Fn fn) {
      for (I i = start; i != end; ++i)
        add_fn(ta, fn(*i));
    }

    /**
     * Checks that arguments to an operator have the correct kind for the
     * operator's inputs.  Since binary operators may be associative, they
     * are allowed to have any number of inputs greater than 2 that match
     * the kind of the binary operator.  Other operators may only have a
     * number of arguments equal to their input count and the kind of each
     * argument must match the corresponding input kind.  This operation
     * has been made generic so that it works with both rules and terms.
     * Each InputIterator must point to a value v for which kind(v) returns
     * a kind.
     *
     * \param op The operator we are checking the inputs of.
     * \param first An input iterator that points to the first argument for
     *        the operator.
     * \param last An input iterator that points to one past the last
     *        argument for the operator.
     */
    template<typename InputIterator>
    void check_well_formed(const op_t& op,
                           InputIterator first, InputIterator last) {
      if (is_binary(op)) {
        // This op may be associative in some contexts and so check that
        // number of subterms is at least 2 and each subterm matches output
        // kind of operator.
        size_t count = 0;
        for (InputIterator i = first; i != last; ++i) {
          if (kind(*i) != output(op))
            sig_error("Kind " + name(kind(*i))
                    + " of subterm for binary operator " + name(op)
                    + " is not expected kind " + name(output(op)) + ".");
          ++count;
        }
        if (count < 2)
          sig_error("Terms for binary operator " + name(op)
                  + " must have at least two subterms.");
      } else {
        // Check that number of subterms matches number of inputs for
        // operator and kinds of subterms match input kinds of operator
        InputIterator i = first;
        op_t::input_iterator iop = inputs_begin(op);
        op_t::input_iterator op_end = inputs_end(op);
        while ((i != last) && (iop != op_end)) {
          if (kind(*i) != *iop)
            sig_error("Kind " + name(kind(*i))
                    + " of subterm for operator " + name(op)
                    + " is not expected input kind " + name(*iop) + ".");
          ++i;
          ++iop;
        }
        if ((i != last) || (iop != op_end))
          sig_error("Subterms for operator " + name(op)
                  + " do not match number of arguments.");
      }
    }

    /**
     * Applies F to any new combination of iterators.
     * I is a bidirectional iterator that points to an iterator range over
     * some type of iterators called the underlying iterator.
     * p is an unary predicate that accepts a vector of underlying iterators.
     * It should throw an exception if it wants to abort processing new
     * combinations.
     */
    template<typename I, typename UnaryPredicate>
    void new_combinations(I first, I last, UnaryPredicate& p) {
      // Get index of last column with unprocessed values.
      I last_new_range = last;
      for (I i = first; i != last; ++i) {
        if (i->begin_new() != i->end())
          last_new_range = i;
      }
      // If there are no ranges with new inputs, then return
      if (last_new_range == last) return;

      // Get type of iterator that incremental range is over.
      typedef typename iterator_traits<I>::value_type::iterator
              element_iterator;

      size_t input_count = std::distance(first, last);
      vector<element_iterator> inputs;
      inputs.reserve(input_count);
      for (I i = first; i != last; ++i)
        inputs.push_back(i->begin());


      typedef typename vector<element_iterator>::const_iterator
              element_vector_const_iter;
      typedef typename vector<element_iterator>::iterator
              element_vector_iter;
      // Points to last input argument.
      element_vector_const_iter last_input = inputs.end() - 1;

      // Points to last assigned input.
      element_vector_iter cur_input = inputs.begin();
      // Stores number of iterators in inputs that point to new value.
      *cur_input = (first == last_new_range)
                 ? first->begin_new()
                 : first->begin();
      // Stores number of assigned arguments that point to new elements.
      size_t new_count = (*cur_input == first->begin_new()) ? 1 : 0;
      // Points to last assigned range.
      I cur_range = first;
      while (inputs[0] != first->end()) {
        // If we have reached end for this argument
        if (*cur_input == cur_range->end()) {
          // Since *cur_input == cur_range->end(), we must be at a new state
          // and so new_count must be decremented.
          --new_count;
          // Goto previous level
          --cur_input;
          --cur_range;
          // Goto next input.
          ++(*cur_input);
        // If we have not yet assigned last input
        } else if (cur_input != last_input) {
          // Goto next level
          ++cur_input;
          ++cur_range;
          // Select initial input for next argument.
          *cur_input = (new_count == 0) && (cur_range == last_new_range)
                     ? cur_range->begin_new()
                     : cur_range->begin();
        // else explore current state.
        } else {
          const vector<element_iterator>& const_inputs = inputs;
          p(const_inputs);
          // Goto next input.
          ++(*cur_input);
        }
        // Increment new_count if we just reached new input.
        if (*cur_input == cur_range->begin_new())
          ++new_count;
      }
    }

    typedef map<kind_t, state_predicate_t> predicate_map_t;
  }

  using namespace impl;

  void check_equal(const kind_t& x, const kind_t& y) {
    if (x != y)
      sig_error("Kinds are not equal.");
  }

  void check_constant(const op_t& op) {
    if (!is_constant(op))
      sig_error(name(op) + " must be a constant.");
  }

  void check_kinds(const kind_t& k, const std::set<state_t>& states) {
    typedef std::set<state_t>::const_iterator state_iter;
    state_iter end = states.end();
    for (state_iter i = states.begin(); i != end; ++i)
      check_equal(kind(*i), k);
  }

  void check_well_formed(const op_t& op,
                         const std::vector<term_t>& subterms) {
    check_well_formed(op, subterms.begin(), subterms.end());
  }

  ostream& operator<<(ostream& o, const term_t& term) {
    o << root(term);
    if (!is_constant(term)) {
      o << "(";
      typedef term_t::subterm_iterator term_iter;
      term_iter begin = subterms_begin(term);
      term_iter end = subterms_end(term);
      // Write first subterm.
      if (begin != end) {
        o << *begin;
        ++begin;
      }
      // Write rest of subterms.
      while (begin != end) {
        o << ", " << *begin;
        ++begin;
      }
      o << ")";
    }
    return o;
  }

  axiom_set_t& axiom_set_t::operator|=(const axiom_set_t& rhs) {
    if ((id_type_ != id_none) && (rhs.id_type_ != id_none)) {
      sig_error("Cannot combine two axiom sets that both have identity \
                 axioms.");
    }
    if ((is_assoc_ || rhs.is_assoc_ || is_comm_ || rhs.is_comm_) &&
        ((rhs.id_type_ == id_left) || (rhs.id_type_ == id_right))) {
      sig_error("If axiom set contains asssociativity or commutativity, it cannot contain a left or right identity.");
    }
    is_assoc_ |= rhs.is_assoc_;
    is_comm_ |= rhs.is_comm_;
    if (rhs.id_type_ != id_none) {
      id_type_ = rhs.id_type_;
      id_symbol_ = rhs.id_symbol_;
    }
    return *this;
  }

  std::ostream& operator<<(ostream& o, const axiom_set_t& axioms) {
    // Indicates if text has been written to stream.
    bool text = false;
    if (is_assoc(axioms)) {
      o << "assoc";
      text = true;
    }
    if (is_comm(axioms)) {
      if (text) o << " ";
      o << "comm";
      text = true;
    }
    // Write text before id symbol if necessary.
    if (text && id_symbol(axioms)) o << " ";
    switch (id_type(axioms)) {
    case id_left:
      o << "left-id: " << *id_symbol(axioms);
      break;
    case id_right:
      o << "right-id: " << *id_symbol(axioms);
      break;
    case id_both:
      o << "id: " << *id_symbol(axioms);
      break;
    case id_none:
      if (!text)
        o << "none";
      break;
    }
    return o;
  }

  typedef map<op_t, set<op_t> > id_symbols_t;

  /** Structure for storing theory implementation. */
  struct theory_impl {
    set<kind_t> kinds;
    set<op_t> ops;
    axiom_map_t axioms;
    /**
     * Multimap from constant symbols to binary operators that have constant
     * symbol as an identity.
     */
    id_symbols_t id_symbols;
  };

  theory_t::theory_t()
    : impl_(new theory_impl) {
  }

  const theory_t::kind_iterator
          add_kind(theory_t& theory, const kind_t& kind) {
    make_unique(theory.impl_);
    return theory.impl_->kinds.insert(kind).first;
  }

  const theory_t::op_iterator add_op(theory_t& theory, const op_t& op) {
    // Check that kinds of op are in theory
    typedef op_t::input_iterator kind_iter;
    for (kind_iter i = inputs_begin(op); i != inputs_end(op); ++i)
      check_member(theory, *i);
    check_member(theory, output(op));
    // Add op to collection
    make_unique(theory.impl_);
    pair<theory_t::op_iterator, bool> result = theory.impl_->ops.insert(op);
    if (result.second) {
      try {
        if (is_binary(op))
          theory.impl_->axioms.insert(make_pair(op, none()));
      } catch (...) {
        theory.impl_->ops.erase(op);
        throw;
      }
    }
    return result.first;
  }

  void set_axioms(theory_t& theory, const op_t& bin_op,
                  const axiom_set_t& new_axioms) {
    // Check to see if new axioms equals old axioms.
    // This also checks that bin_op is in the theory.
    if (new_axioms == axioms(theory, bin_op))
      return;

    // Since axioms are different we know that if bin_op is not binary, then
    // new_axioms do not equal none().  This is an error, so now we just
    // check that bin_op is binary.
    check_binary(bin_op);
    // If there is an identity symbol, check that it is in the theory.
    if (id_symbol(new_axioms))
      check_member(theory, *id_symbol(new_axioms));

    make_unique(theory.impl_);
    axiom_set_t& cur_axioms = theory.impl_->axioms.find(bin_op)->second;

    id_symbols_t& id_symbols = theory.impl_->id_symbols;
    // Add new id to id_symbols (can throw bad_alloc)
    boost::optional<op_t> new_id = id_symbol(new_axioms);
    if (new_id) id_symbols[*new_id].insert(bin_op);

    // Remove previous identity (cannot throw).
    boost::optional<op_t> old_id = id_symbol(cur_axioms);
    if (old_id) id_symbols[*old_id].erase(bin_op);

    // Assign new axioms (cannot throw)
    cur_axioms = new_axioms;
  }

  const axiom_set_t& axioms(const theory_t& theory, const op_t& op) {
    if (is_binary(op)) {
      axiom_map_t::const_iterator i = theory.impl_->axioms.find(op);
      if (i == theory.impl_->axioms.end())
        sig_error(name(op) + " is not in theory.");
      return i->second;
    } else {
      return none();
    }
  }

  theory_t::kind_iterator kinds_begin(const theory_t& theory) {
    return theory.impl_->kinds.begin();
  }

  theory_t::kind_iterator kinds_end(const theory_t& theory) {
    return theory.impl_->kinds.end();
  }

  bool member(const theory_t& theory, const kind_t& kind) {
    return theory.impl_->kinds.count(kind) > 0;
  }

  bool member(const theory_t& theory, const op_t& op) {
    return theory.impl_->ops.count(op) > 0;
  }

  theory_t::op_iterator ops_begin(const theory_t& theory) {
    return theory.impl_->ops.begin();
  }

  theory_t::op_iterator ops_end(const theory_t& theory) {
    return theory.impl_->ops.end();
  }

  ostream& operator<<(ostream& o, const theory_t& theory) {
    decl_writer writer(&o, &theory);
    for_each(kinds_begin(theory), kinds_end(theory), writer);
    for_each(  ops_begin(theory),   ops_end(theory), writer);
    return o;
  }

  const set<op_t>& id_symbols(const id_symbols_t& id_syms, const op_t& id) {
    id_symbols_t::const_iterator i = id_syms.find(id);
    if (i != id_syms.end()) {
      return i->second;
    } else {
      static set<op_t> empty_set;
      return empty_set;
    }
  }

  theory_t::op_iterator id_contexts_begin(const theory_t& theory,
                                          const op_t& id) {
    check_member(theory, id);
    return id_symbols(theory.impl_->id_symbols, id).begin();
  }

  theory_t::op_iterator id_contexts_end(const theory_t& theory,
                                        const op_t& id) {
    check_member(theory, id);
    return id_symbols(theory.impl_->id_symbols, id).end();
  }

  bool operator==(const theory_t& lhs, const theory_t& rhs) {
    return (lhs.impl_ == rhs.impl_)
        || equal(kinds_begin(lhs), kinds_end(lhs),
                 kinds_begin(rhs), kinds_end(rhs))
        && equal(ops_begin(lhs), ops_end(lhs),
                 ops_begin(rhs), ops_end(rhs),
                 ops_equivalent(lhs, rhs));
  }

  bool models(const state_predicate_t& pred, const set<state_t>& model) {
    return apply_visitor(predicate_models_visitor(model), pred);
  }

  ostream& operator<<(ostream& o, const state_predicate_t& p) {
    apply_visitor(print_visitor(o), p);
    return o;
  }

  void check_well_formed(const op_t& op,
                         const std::vector<state_t>& lhs_states,
                         const state_t& rhs) {
    check_well_formed(op, lhs_states.begin(), lhs_states.end());
    check_equal(output(op), kind(rhs));
  }

  struct ta_impl {
    ta_impl(theory_t t)
      : theory(t) {
    }
    const theory_t theory;
    set<state_t> states;
    predicate_map_t predicates;
    vector<erule_t> erules;
    vector<rule_t> rules;
  };

  ta_t::ta_t(const theory_t& theory)
    : impl_(new ta_impl(theory)) {
    typedef theory_t::kind_iterator kind_iter;
    for (kind_iter i = kinds_begin(theory); i != kinds_end(theory); ++i)
      impl_->predicates.insert(make_pair(*i, state_predicate_t(*i, false)));
  }

  const theory_t& theory(const ta_t& ta) {
    return ta.impl_->theory;
  }

  const ta_t::state_iterator states_begin(const ta_t& ta) {
    return ta.impl_->states.begin();
  }

  const ta_t::state_iterator states_end(const ta_t& ta) {
    return ta.impl_->states.end();
  }

  bool member(const ta_t& ta, const state_t& state) {
    return ta.impl_->states.count(state) > 0;
  }

  const ta_t::state_iterator
          add_state(ta_t& ta, const state_t& state) {
    check_member(theory(ta), kind(state));
    make_unique(ta.impl_);
    return ta.impl_->states.insert(state).first;
  }

  const state_predicate_t& predicate(const ta_t& ta, const kind_t& kind) {
    predicate_map_t::const_iterator i = ta.impl_->predicates.find(kind);
    if (i == ta.impl_->predicates.end())
      sig_error(name(kind) + " is not in theory.");
    return i->second;
  }

  void set_predicate(ta_t& ta, const state_predicate_t& pred) {
    make_unique(ta.impl_);
    predicate_map_t::iterator i = ta.impl_->predicates.find(kind(pred));
    if (i != ta.impl_->predicates.end()) {
      check_states(ta, pred);
      i->second = pred;
    } else {
      sig_error(name(kind(pred)) + " is not in theory.");
    }
  }

  const ta_t::erule_iterator erules_begin(const ta_t& ta) {
    return ta.impl_->erules.begin();
  }

  const ta_t::erule_iterator erules_end(const ta_t& ta) {
    return ta.impl_->erules.end();
  }

  void add_erule(ta_t& ta, const erule_t& erule) {
    check_member(ta, lhs(erule));
    check_member(ta, rhs(erule));
    make_unique(ta.impl_);
    ta.impl_->erules.push_back(erule);
  }

  const ta_t::rule_iterator rules_begin(const ta_t& ta) {
    return ta.impl_->rules.begin();
  }

  const ta_t::rule_iterator rules_end(const ta_t& ta) {
    return ta.impl_->rules.end();
  }

  void add_rule(ta_t& ta, const rule_t& rule) {
    check_member(theory(ta), op(rule));
    axiom_set_t op_axioms = axioms(theory(ta), op(rule));
    if (!is_assoc(op_axioms)
              && (lhs_state_count(rule) != input_count(op(rule)))) {
      sig_error("Rule operator is not associative and number of states does \
                 not equal number of arguments.");
    }
    // Check that each state in left-hand-side is in automaton.
    typedef rule_t::lhs_state_iterator state_iter;
    state_iter end = lhs_states_end(rule);
    for (state_iter i = lhs_states_begin(rule); i != end; ++i)
      check_member(ta, *i);
    check_member(ta, rhs(rule));

    make_unique(ta.impl_);
    if (is_assoc(op_axioms)) {
      // Break left hand side states down and introduce new states so that
      // each rule has at most two arguments.
      kind_t k = output(op(rule));
      rule_t::lhs_state_iterator next = lhs_states_begin(rule);
      state_t prev = *(next++);
      rule_t::lhs_state_iterator last = lhs_states_end(rule) - 1;
      while (next != last) {
        state_t new_state(k, "fresh_state");
        ta.impl_->rules.push_back(
                make_binary_rule(op(rule), prev, *next, new_state));
        prev = new_state;
        ++next;
      }
      ta.impl_->rules.push_back(
              make_binary_rule(op(rule), prev, *next, rhs(rule)));
    } else {
      ta.impl_->rules.push_back(rule);
    }
  }

  const ta_t operator!(const ta_t& ta) {
    ta_t result = ta;

    typedef theory_t::kind_iterator kind_iter;
    const theory_t& cur_theory = theory(ta);
    kind_iter end = kinds_end(cur_theory);
    for (kind_iter i = kinds_begin(cur_theory); i != end; ++i)
      set_predicate(result, !predicate(ta, *i));
    return result;
  }

  ta_t& operator&=(ta_t& lhs, const ta_t& rhs) {
    check_equal(theory(lhs), theory(rhs));
    // Generate substitutions for states that are in both lhs and rhs
    const state_subst_t subst = make_state_subst(lhs, rhs);
    add_range(states_begin(rhs), states_end(rhs), add_state, lhs, subst);
    // Add renamed states in rhs.
    // Intersect predicates in lhs with renamed predicate in rhs.
    theory_t::kind_iterator k_begin = kinds_begin(theory(lhs));
    theory_t::kind_iterator k_end   =   kinds_end(theory(lhs));
    for (theory_t::kind_iterator i = k_begin; i != k_end; ++i)
      set_predicate(lhs, predicate(lhs, *i) & subst(predicate(rhs, *i)));
    // Add renamed rules in rhs to lhs.
    add_range(erules_begin(rhs), erules_end(rhs), add_erule, lhs, subst);
    add_range( rules_begin(rhs),  rules_end(rhs),  add_rule, lhs, subst);
    return lhs;
  }

  ta_t& operator|=(ta_t& lhs, const ta_t& rhs) {
    check_equal(theory(lhs), theory(rhs));
    // Generate substitutions for states that are in both lhs and rhs
    const state_subst_t subst = make_state_subst(lhs, rhs);
    // Add renamed states in rhs.
    add_range(states_begin(rhs), states_end(rhs), add_state, lhs, subst);
    // Intersect predicates in lhs with renamed predicate in rhs.
    theory_t::kind_iterator k_begin = kinds_begin(theory(lhs));
    theory_t::kind_iterator k_end   =   kinds_end(theory(lhs));
    for (theory_t::kind_iterator i = k_begin; i != k_end; ++i)
      set_predicate(lhs, predicate(lhs, *i) | subst(predicate(rhs, *i)));
    // Add renamed rules in rhs to lhs.
    add_range(erules_begin(rhs), erules_end(rhs), add_erule, lhs, subst);
    add_range( rules_begin(rhs),  rules_end(rhs),  add_rule, lhs, subst);
    return lhs;
  }

  ostream& operator<<(ostream& o, const ta_t& ta) {
    o << theory(ta);
    decl_writer writer(&o, &theory(ta));
    for_each(states_begin(ta), states_end(ta), writer);
    theory_t::kind_iterator k_begin = kinds_begin(theory(ta));
    theory_t::kind_iterator k_end   =   kinds_end(theory(ta));
    for (theory_t::kind_iterator i = k_begin; i != k_end; ++i)
      writer(predicate(ta, *i));
    for_each(erules_begin(ta), erules_end(ta), writer);
    for_each( rules_begin(ta),  rules_end(ta), writer);
    return o;
  }
}
