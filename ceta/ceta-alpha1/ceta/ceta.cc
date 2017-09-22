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
#include "ceta.hh"

#include <functional>
#include <list>
#include <stdexcept>
#include <sstream>

#include <boost/bind.hpp>
#include <boost/function_output_iterator.hpp>
#include <boost/none.hpp>
#include <boost/iterator/transform_iterator.hpp>

#include "bi_graph.hh"
#include "closure.hh"
#include "parikh.hh"
#include "sls.hh"
#include "writer.hh"

using namespace std;
using namespace ceta::closure;
using namespace ceta::cfg;

namespace ceta {
  namespace impl {
    /**
     * Signal that a logical error occurred in the execution of the program
     * by printing an error message and segfaulting.
     */
    static void sig_error(const std::string& msg) NO_RETURN;

    static void sig_error(const std::string& msg) {
//      cerr << msg << endl;
//      *(static_cast<int*>(NULL)) = 2;
      throw logic_error(msg);
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

    /** Returns true if distance(first1, last1) == distance(first2, last2)
     * and elements in predicate returns true when testing pairs of elements
     * in ranges [first1 ... last1) and [first2 ... last2).
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
     * Wraps a substitution in a unary functor that takes a state as input,
     * generates a new state, and appends a binding to the substitution from
     * the old state to the new state.
     */
    class binding_appender {
    public:
      /** Construct a new appender given a pointer to substitution. */
      binding_appender(state_subst_t* subst)
        : subst_(subst) {
      }
      /** 
       * Creates new state, and appends binding from state to new state to
       * substitution.
       */
      void operator()(const state_t& state) {
        state_t new_state(kind(state), name(state) + "'");
        subst_->set(state, new_state);
      }
    private:
      /** Pointer to substitution. */
      state_subst_t* subst_;
    };
  
    /** 
     * Constructs a state substitution mapping to rename states that appear
     * in both automata to fresh states.
     */
    const state_subst_t make_state_subst(const ta_t& x, const ta_t& y) {
      state_subst_t result;
      typedef theory_t::kind_iterator kind_iter;
      typedef boost::function_output_iterator<binding_appender>
              appender_iter;
  
      std::set_intersection(states_begin(x), states_end(x),
                            states_begin(y), states_end(y),
                            appender_iter(&result));
      return result;
    }
  
    /** 
     * Visitor to components of a state predicate to determine if set is a
     * model of predicate.
     */
    class state_models_visitor {
    public:
      typedef bool result_type;
      state_models_visitor(const std::set<state_t>& model)
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
            { OR_PRIORITY = 1, AND_PRIORITY = 2, DEFAULT_PRIORITY = 3 };
    
    /** 
     * Visitor to components of state predicate to determine priority of
     * top operator of predicate.
     */
    struct priority_visitor {
      typedef priority_t result_type;

      template<typename T>
      priority_t operator()(const T&) const {
        return DEFAULT_PRIORITY;
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

    /**
     * Visits elements of components of state predicate to write to ostream.
     */
    class print_visitor {
    public:
      typedef void result_type;
      print_visitor(ostream* o)
        : o_(o) {
      }
      void operator()(bool value) const {
        *o_ << (value ? "true" : "false");
      }
      void operator()(const state_t& state) const {
        *o_ << state;
      }
      void operator()(const not_predicate_t& pred) const {
        *o_ << "!";
        print(pred.arg, DEFAULT_PRIORITY);
      }
      void operator()(const and_predicate_t& pred) const {
        print(pred.lhs, AND_PRIORITY);
        *o_ << " & ";
        print(pred.rhs, AND_PRIORITY);
      }
      void operator()(const or_predicate_t& pred) const {
        print(pred.lhs, OR_PRIORITY);
        *o_ << " | ";
        print(pred.rhs, OR_PRIORITY);
      }
    private:
      void print(const state_predicate_t& pred, 
                 priority_t parent_priority) const {
        priority_t pred_priority = priority(pred);
        if (pred_priority < parent_priority) *o_ << "(";
        apply_visitor(*this, pred);
        if (pred_priority < parent_priority) *o_ << ")";
      }
      ostream* o_;
    };

    static
    void check_member(const ta_t& ta, const state_t& state) {
      if (!member(ta, state)) 
        sig_error("State " + name(state) + " is not a member of automaton.");
    }

    /**
     * Visits components of state predicate to check that each state is in
     * the automaton.
     */
    struct check_state_visitor {
      typedef void result_type;
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

    struct rename_visitor {
      typedef pair<const state_predicate_t, bool>  result_type;

      rename_visitor(const state_subst_t* subst,
                     const state_predicate_t& context)
        : subst_(subst), context_(context) {
      }
      result_type operator()(bool value) const {
        return make_pair(context_, false);
      }
      result_type operator()(const state_t& state) const {
        state_t new_state = (*subst_)(state);
        if (new_state != state) {
          return result_type(state_predicate_t(new_state), true);
        } else {
          return result_type(context_, false);
        }
      }
      result_type operator()(const not_predicate_t& pred) const {
        result_type arg_result 
          = apply_visitor(rename_visitor(subst_, pred.arg), pred.arg);
        if (arg_result.second) {
          return result_type(! arg_result.first, true);
        } else {
          return result_type(context_, false);
        }
      }
      result_type operator()(const and_predicate_t& pred) const {
        result_type lhs_result 
          = apply_visitor(rename_visitor(subst_, pred.lhs), pred.lhs);
        result_type rhs_result 
          = apply_visitor(rename_visitor(subst_, pred.lhs), pred.rhs);
        if (lhs_result.second || rhs_result.second) {
          return result_type(lhs_result.first & rhs_result.first, true);
        } else {
          return result_type(context_, false);
        }
      }
      result_type operator()(const or_predicate_t& pred) const {
        result_type lhs_result 
          = apply_visitor(rename_visitor(subst_, pred.lhs), pred.lhs);
        result_type rhs_result 
          = apply_visitor(rename_visitor(subst_, pred.lhs), pred.rhs);
        if (lhs_result.second || rhs_result.second) {
          return result_type(lhs_result.first | rhs_result.first, true);
        } else {
          return result_type(context_, false);
        }
      }
    private:
      const state_subst_t* subst_;
      const state_predicate_t context_;
    };
 
    /**
     * Returns a copy of a state predicate in which each state has been
     * changed using the substitution.
     */
    static
    const state_predicate_t apply(const state_subst_t& subst,
                                  const state_predicate_t& pred) {
      return apply_visitor(rename_visitor(&subst, pred), pred).first;
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

      decl_writer(ostream* o)
        : o_(o) {
      }
      void operator()(const kind_t& kind) {
        *o_ << "kind " << name(kind) << endl;
      }
      void operator()(const op_t& op) {
        *o_ << "op " << name(op) << " : "
            << make_range_writer(inputs_begin(op), inputs_end(op)) 
            << " -> " << output(op) << endl;
      }
      void operator()(const state_t& state) {
        *o_ << "state " << name(state) << " -> " << kind(state) << endl;
      }
      void operator()(const state_predicate_t& pred) {
        *o_ << "accept " << kind(pred) << " : " << pred << endl;
      }
      void operator()(const erule_t& erule) {
        *o_ << "rl " << lhs(erule) << " -> " << rhs(erule) << endl;
      }
      void operator()(const rule_t& rule) {
        *o_ << "rl " << op(rule);
        if (lhs_states_begin(rule) != lhs_states_end(rule)) {
          *o_ << "(" 
            << make_range_writer(lhs_states_begin(rule),
                                 lhs_states_end(rule))
            << ")";
        }
      }
    private:
      ostream* o_;
    };

    /** 
     * Creates new erule by applying substitution to lhs and rhs of existing
     * erule.
     */
    static
    const erule_t apply(const state_subst_t& subst, const erule_t& erule) {
      return erule_t(subst(lhs(erule)), subst(rhs(erule)));
    }
  
    /**
     * Creates new rule by applying substitution to lhs and rhs of existing
     * rule.
     */
    static
    const rule_t apply(const state_subst_t& subst, const rule_t& rule) {
      typedef const state_t& state_ref;
      typedef boost::transform_iterator<state_subst_t, 
                                        rule_t::lhs_state_iterator,
                                        state_ref>
              trans_iter;
      trans_iter begin(lhs_states_begin(rule), subst);
      trans_iter end(lhs_states_end(rule), subst);
      return rule_t(op(rule), begin, end, subst(rhs(rule)));
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

    typedef std::pair<op_t, size_t> context_t;

    static inline
    context_t make_context(const op_t& op, size_t pos) {
      return make_pair(op, pos);
    }

    typedef vector< pair< term_t, set<state_t> > > set_vector_t;

    class reachable_states_t {
    public:
      typedef set_vector_t::const_iterator iterator;

      /** Construct an empty set of reachable states for automaton. */
      reachable_states_t(const ta_t& ta)
        :ta_(ta) {
      }


      /** Returns true if op is identity for more than one binary symbol. */
      bool is_multiple_identity(const theory_t& theory, const op_t& op) {
        theory_t::op_iterator begin = id_contexts_begin(theory, op);
        theory_t::op_iterator end = id_contexts_end(theory, op);
        if (begin == end)
          return false;
        ++begin;
        return (begin != end);
      }

      void add(const term_t& term, const set<state_t>& states) {
        kind_t k = kind(term);
        set_map_t::iterator i = set_map_.find(states);
        op_t top_op = op(term);
        // If we have already added this state set
        if (i != set_map_.end()) {
          // Check to see if previous term was potentially invallid.
          if (i->second && (top_op != *i->second)) {
            op_t new_op = *i->second;
            const axiom_set_t& top_ax = axioms(theory(ta_), top_op);
            const axiom_set_t& new_ax = axioms(theory(ta_), new_op);

            const boost::optional<op_t>& top_id = id_symbol(top_ax);
            const boost::optional<op_t>& new_id = id_symbol(new_ax);

            // If top_op is associative and new_op is its identity.
            if (is_assoc(top_ax) && top_id && (new_op == *top_id)) {
              // Do nothing since top_op current term is usable in any
              // context the new term is usable in.
            // If new_op is associative and top_op is its identity.
            } else if (is_assoc(new_ax) && new_id && (top_op == *new_id)) {
              // If top_op is the identity for another symbol, then this
              // state set will potentially allow reaching more states
              // through new term, so we use it.
              if (is_multiple_identity(theory(ta_), top_op)) {
                vector_map_[k].push_back(make_pair(term, states));
                i->second = new_op;
              }
            } else {
              // Between two terms, set must be valid in every context
              vector_map_[k].push_back(make_pair(term, states));
              i->second = boost::none;
            }
          }
        } else {
          vector_map_[k].push_back(make_pair(term, states));
          try {
            boost::optional<op_t> set_op;
            bool potentially_invalid = is_assoc(axioms(theory(ta_), top_op))
                                        || is_identity(theory(ta_), top_op);
            if (potentially_invalid)
              set_op = op(term);
            set_map_.insert(make_pair(states, set_op));
            // Check to see if added is a counter example.
            if (models(predicate(ta_, k), states))
              throw test_result_t(term, states);
          } catch (...) {
            set_map_.erase(states);
            vector_map_[k].pop_back();
            throw;
          }
        }
      }

      /**
       * Return a random access iterator pointing to first set of reachable
       * state sets for kind.
       */
      iterator begin(kind_t k) const {
        return set_vector(k).begin();
      }

      /**
       * Return a random access iterator pointing one past the last set of
       * reachable state sets for kind.
       */
      iterator end(kind_t k) const {
        return set_vector(k).end();
      }
    private:
      typedef map<set<state_t>, boost::optional<op_t> > set_map_t;
      typedef map<kind_t, set_vector_t> vector_map_t; 
      const set_vector_t& set_vector(kind_t k) const {
        vector_map_t::const_iterator i = vector_map_.find(k);
        if (i != vector_map_.end()) {
          return i->second;
        } else {
          static const set_vector_t empty_vector;
          return empty_vector;
        }
      }

      const ta_t ta_;
      set_map_t set_map_;
      vector_map_t vector_map_;
    };

    size_t state_count(const reachable_states_t& states, kind_t k) {
      return std::distance(states.begin(k), states.end(k));
    }

    /**
     * Stores the reachable states intersected with the a subset of the
     * states.
     */
    class reachable_image_t {
    public:
      typedef set_vector_t::const_iterator iterator;
        
      reachable_image_t(const set<op_t>& bad_ops, 
                        const set<state_t>& allowed_states)
        : bad_ops_(bad_ops),
          allowed_states_(allowed_states) {
      }
    
      void add(const pair< term_t, set<state_t> >& new_pair) {
        add(new_pair.first, new_pair.second);
      }

      void add(const term_t& term, const set<state_t>& states) {
        // Check that this term is in valid context.
        if (bad_ops_.count(op(term)) == 0) {
          /** Compute intersection of set and allowed_states. */
          set<state_t> subset;
          set_intersection(allowed_states_.begin(), allowed_states_.end(),
                           states.begin(), states.end(),
                           inserter(subset, subset.begin()));
          bool added = set_image_.insert(subset).second;
          if (added)
            set_vector_.push_back(make_pair(term, subset));
        }
      }

      const set<state_t>& states() const {
        return allowed_states_;
      }

      iterator begin() const {
        return set_vector_.begin();
      }

      iterator end() const {
        return set_vector_.end();
      }
    private:
      /**
       * Set of operators that may not appear at the top of a term if it is
       * to be added.
       */
      set<op_t> bad_ops_;
      /** The set of states that are allowed to be in a reachable set. */
      set<state_t> allowed_states_;
      /**
       * The set of sets of states that are known to be reachable 
       * intersected with the states in rule_states.
       */
      set< set<state_t> > set_image_;
      /**
       * The known states and the term used to reach the known states
       * stored in the order it was added.
       */
      set_vector_t set_vector_;
    };
    size_t state_count(const reachable_image_t& image) {
      return std::distance(image.begin(), image.end());
    }
      

    class op_explorer {
    public:
      op_explorer(const theory_t& theory,
                  const epsilon_closure_t& closure,
                  const op_t& op,
                  const vector<rule_t>& rules,
                  reachable_states_t& reachable_states)
        : theory_(theory),
          closure_(&closure),
          op_(op),
          rules_(&rules),
          reachable_states_(&reachable_states) {
      }
      const op_t& op() {
        return op_;
      }
      virtual ~op_explorer() {
      }
      virtual void explore() = 0;
    protected:
      const theory_t theory_;
      /** Epsilon closure for automaton. */
      const epsilon_closure_t* closure_;
      /** Operator for explorer. */
      const op_t op_;
      /** Rules for operator. */
      const vector<rule_t>* rules_;
      /** Pointer to current set of reachable states. */
      reachable_states_t* reachable_states_;
    };

    /** Returns bad operators for axioms of a operator. */
    const set<op_t> bad_ops(const op_t& op,
                            const axiom_set_t& axioms,
                            size_t pos = 0) {
      set<op_t> result;
       if (is_assoc(axioms))
        result.insert(op);
      id_type_t type = id_type(axioms);
      if ((type == id_left) && (pos == 0) ||
          (type == id_right) && (pos == 1) ||
          (type == id_both)) {
        result.insert(*id_symbol(axioms));
      }
      return result;
    }

    /**
     * Returns the set of states that appear as a lhs state of a rule in the
     * range [first last).
     */
    template<typename RuleInputIterator>
    static inline
    set<state_t> lhs_states(RuleInputIterator first,
                            RuleInputIterator last) {
      set<state_t> result;
      for (RuleInputIterator i = first; i != last; ++i)
        result.insert(lhs_states_begin(*i), lhs_states_end(*i));
      return result;
    }

    /**
     * Returns the set of states that appear on rhs of a rule in the range
     * [first last).
     */
    template<typename RuleInputIterator>
    static inline
    set<state_t> rhs_states(RuleInputIterator first,
                            RuleInputIterator last) {
      set<state_t> result;
      for (RuleInputIterator i = first; i != last; ++i)
        result.insert(rhs(*i));
      return result;
    }

    /**
     * Returns the set of states that appear in the lhs state at index arg
     * of a rule in the range [first last).
     */
    template<typename RuleInputIterator>
    static inline
    set<state_t> lhs_states(RuleInputIterator first,
                            RuleInputIterator last, size_t arg) {
      set<state_t> result;
      for (RuleInputIterator i = first; i != last; ++i)
        result.insert(lhs_state(*i, arg));
      return result;
    }

    /** Adds each element in range [first last) to list. */
    template<typename InputIterator, typename L>
    static
    void add_each(InputIterator first, InputIterator last, L& list) {
      for (InputIterator i = first; i != last; ++i)
        list.add(*i);
    }

    /** 
     * A triple containing three iterators that defines a range that is
     * processed by some incremental algorithm.  The range is from
     * [begin end), but there is an additional pointer to an iterator in the
     * range [begin end] that points to the first value that has not been
     * processed by the algorithm.  If begin_new equals begin, then the
     * algorithm has processed no elements so far.  If begin_new equals end,
     * then the algorithm has processed every element.
     */
    template<typename I>
    class incremental_range {
    public:
      typedef I iterator;

      incremental_range(I begin, I begin_new, I end) 
        : begin_(begin),
          begin_new_(begin_new),
          end_(end) {
      };
      /** Returns iterator that points to first element in range. */
      I begin() {
        return begin_;
      }
      I begin_new() {
        return begin_new_;
      }
      I end() {
        return end_;
      }
    private:
      I begin_;
      I begin_new_;
      I end_;
    };

    /**
     * Applies F to any new combination of iterators.
     * I is a bidirectional iterator that points to an iterator range over
     * some type of iterators called the underlying iterator.
     * p is an unary predicate that accepts a vector of underlying iterators.
     * It should throw an exception if it wants to abort processing new
     * combinations.
     */
    template<typename I, typename UnaryPredicate>
    void new_combinations(I first, I last, UnaryPredicate p) {
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

      vector<element_iterator> inputs(std::distance(first, last));
      
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

    class free_explorer : public op_explorer {
    public:
      free_explorer(const theory_t& theory,
                    const epsilon_closure_t& closure,
                    const op_t& op,
                    const vector<rule_t>& rules,
                    reachable_states_t& reachable_states)
        : op_explorer(theory, closure, op, rules, reachable_states),
          processed_counts_(input_count(op), 0) {
        op_t::input_iterator end = inputs_end(op);
        const axiom_set_t& op_axioms = axioms(theory, op);
        reachable_images_.reserve(input_count(op));
        for (op_t::input_iterator i = inputs_begin(op); i != end; ++i) {
          size_t cur_idx = reachable_images_.size();
          reachable_images_.push_back(reachable_image_t(
                  bad_ops(op, op_axioms, cur_idx),
                  lhs_states(rules_->begin(), rules_->end(), cur_idx)));
        }
      }

      virtual void explore() {
        typedef reachable_image_t::iterator image_iter;
        // Range for each input.
        vector< incremental_range<image_iter> > ranges;
        ranges.reserve(input_count(op_));
        // New processed count for each input
        vector<size_t> new_processed_counts;
        new_processed_counts.reserve(input_count(op_));
        // Update image for each input
        for (size_t i = 0; i != input_count(op_); ++i) {
          reachable_image_t& image = reachable_images_[i];
          kind_t k = input(op_, i);

          size_t old_size = state_count(image);
          // Add new reachable states for kind of input to image for input
          add_each(reachable_states_->begin(k) + processed_counts_[i],
                   reachable_states_->end(k),
                   image);
          // Add range for input
          ranges.push_back(incremental_range<image_iter>(
                     image.begin(), image.begin() + old_size, image.end()));
          // Update processed counts
          new_processed_counts.push_back(state_count(*reachable_states_, k));
        }
        
        // Explore all new combinations 
        new_combinations(ranges.begin(), ranges.end(), *this);
        // Update processed counts
        processed_counts_ = new_processed_counts;
      }

      /** Add reachable states for inputs to reachables_states_ */
      void operator()(const vector<reachable_image_t::iterator>& inputs) {
        set<state_t> states;
        typedef vector<rule_t>::const_iterator rule_iter;
        for (rule_iter i = rules_->begin(); i != rules_->end(); ++i) {
          if (should_accept(*i, inputs)) {
            const set<state_t>& new_set = reachables(*closure_, rhs(*i));
            states.insert(new_set.begin(), new_set.end());
          }
        }
        vector<term_t> subterms;
        subterms.reserve(inputs.size());
        typedef vector<reachable_image_t::iterator>::const_iterator
                input_iter;
        for (input_iter i = inputs.begin(); i != inputs.end(); ++i)
          subterms.push_back((*i)->first);
        reachable_states_->add(term_t(op_, subterms.begin(), subterms.end()),
                               states);
      }
    private:
      bool should_accept(const rule_t& rule, 
                         const vector<reachable_image_t::iterator>& inputs) {
        typedef rule_t::lhs_state_iterator state_iter;
        typedef vector<reachable_image_t::iterator>::const_iterator
                input_iter;
        input_iter cur_input = inputs.begin();
        state_iter cur_state = lhs_states_begin(rule);
        state_iter end_state = lhs_states_end(rule);
        while (cur_state != end_state) {
          // Return false if current input set does not contain current
          // state.
          if ((*cur_input)->second.count(*cur_state) == 0)
            return false;
          ++cur_state;
          ++cur_input;
        }
        return true;
      }
      /** 
       * The number of state sets in reachable_states_ that we have processed
       * for each input.
       */
      vector<size_t> processed_counts_;
      /** 
       * The reachable states for each input intersected with the states
       * that are used by that input.
       */
      vector<reachable_image_t> reachable_images_;
    };

    class comm_explorer : public op_explorer {
    public:
      comm_explorer(const theory_t& theory,
                    const epsilon_closure_t& closure,
                    const op_t& op,
                    const vector<rule_t>& rules,
                    reachable_states_t& reachable_states)
        : op_explorer(theory, closure, op, rules, reachable_states),
          processed_count_(0),
          image_(bad_ops(op, axioms(theory, op)),
                 lhs_states(rules.begin(), rules.end())) {
      }

      virtual void explore() {
        typedef reachable_image_t::iterator image_iter;
        kind_t k = output(op_);
        size_t old_size = state_count(image_);
        add_each(reachable_states_->begin(k) + processed_count_,
                 reachable_states_->end(k),
                 image_);
        size_t new_processed_count = state_count(*reachable_states_, k);

        // Explore all new combinations 
        image_iter img_begin     = image_.begin();
        image_iter img_new_begin = image_.begin() + old_size;
        image_iter img_end       = image_.end();
        // For each new state in image
        for (image_iter i = img_new_begin; i != img_end; ++i) {
          // For every state added before i.
          for (image_iter j = img_begin; j != i + 1; ++j) {
            explore(*i, *j);
          }
        }
        // Update processed counts
        processed_count_ = new_processed_count;
      }
    private:
      typedef pair< term_t, set<state_t> > reachable_pair;
      /** Add reachable pair from x and y to reachable states. */
      void explore(const reachable_pair& x, const reachable_pair& y) {
        set<state_t> states;
        typedef vector<rule_t>::const_iterator rule_iter;
        for (rule_iter i = rules_->begin(); i != rules_->end(); ++i) {
          if (should_accept(*i, x.second, y.second)) {
            const set<state_t>& new_set = reachables(*closure_, rhs(*i));
            states.insert(new_set.begin(), new_set.end());
          }
        }
        const term_t subterms[] = { x.first, y.first };
        reachable_states_->add(term_t(op_, subterms, subterms + 2),
                               states);
      }

      bool should_accept(const rule_t& rule, const set<state_t>& x,
                         const set<state_t>& y) {
        const state_t& lhs0 = lhs_state(rule, 0);
        const state_t& lhs1 = lhs_state(rule, 1);
        return (x.count(lhs0) > 0) && (y.count(lhs1) > 0)
            || (x.count(lhs1) > 0) && (y.count(lhs0) > 0);
      }

      /** 
       * The number of state sets in reachable_states_ that we have
       * processed.
       */
      size_t processed_count_;
      /** 
       * The reachable states intersected with the states that appear on
       * the left-hand-side of rule for operator.
       */
      reachable_image_t image_;
    };

    class assoc_explorer : public op_explorer {
    public:
      assoc_explorer(const theory_t& theory,
                     const epsilon_closure_t& closure,
                     const op_t& op,
                     const vector<rule_t>& rules,
                     reachable_states_t& reachable_states)
        : op_explorer(theory, closure, op, rules, reachable_states) {
        sig_error("Cannot test purely associative ops");
      }
      virtual void explore() {
        // Do nothing
      }
    };

    class AC_explorer : public op_explorer {
    public:
      AC_explorer(const theory_t& theory,
                    const epsilon_closure_t& closure,
                    const op_t& op,
                    const vector<rule_t>& rules,
                    reachable_states_t& reachable_states)
        : op_explorer(theory, closure, op, rules, reachable_states),
          processed_count_(0),
          image_(bad_ops(op, axioms(theory, op)),
                 lhs_states(rules.begin(), rules.end())),
          rhs_states_(rhs_states(rules.begin(), rules.end())) {

        // Add states to grammar.
        add_states_to_grammar(image_.states());
        add_states_to_grammar(rhs_states_);
        
        // Add epsilon rules to grammar.
        typedef nonterminal_map_t::const_iterator nt_iter;
        nt_iter ntm_begin = nonterminal_map_.begin();
        nt_iter ntm_end = nonterminal_map_.end();
        for (nt_iter i = ntm_begin; i != ntm_end; ++i) {
          for (nt_iter j = ntm_begin; j != ntm_end; ++j) {
            erule_t erule(i->first, j->first);
            if (is_reachable(closure, erule_t(i->first, j->first)))
              grammar_.add_transition(i->second, j->second);
          }
        }
        
        // Add regular rules to grammar.
        typedef vector<rule_t>::const_iterator rule_iter;
        for (rule_iter i = rules.begin(); i != rules.end(); ++i) {
          // Add *i to grammar
          symbol_t lhs_symbols[] = {
            find_symbol(lhs_state(*i, 0)),
            find_symbol(lhs_state(*i, 1))
          };
          symbol_t rhs_sym = find_symbol(rhs(*i));
          grammar_.add_transition(lhs_symbols, lhs_symbols + 2, rhs_sym);
        }
      }

      /**
       * Explore new reachable states.  Note that if this operation throws
       * an exception, the explorer will become unusable.
       */
      virtual void explore() {
        kind_t k = output(op_);
        size_t old_size = state_count(image_);
        // Add new states in reachable_states_ to image
        add_each(reachable_states_->begin(k) + processed_count_,
                 reachable_states_->end(k),
                 image_);
        // Update processed count
        processed_count_ = state_count(*reachable_states_, k);

        // Add new states in image to grammar.
        typedef reachable_image_t::iterator image_iter;
        image_iter img_begin = image_.begin();
        image_iter img_end   = image_.end();
        size_t cur_idx = old_size;
        for (image_iter i = img_begin + old_size; i != img_end; ++i) {
          const set<state_t>& cur_set = i->second;
          // Add new terminal symbol to grammar.
          ostringstream o;
          o << cur_set;
          const string s = o.str();
          symbol_t nt_sym = grammar_.add_terminal(s.c_str());
          
          // Add transitions from symbol to each symbol of states in cur_set
          typedef set<state_t>::const_iterator state_iter;
          state_iter set_end = cur_set.end();
          for (state_iter j = cur_set.begin(); j != set_end; ++j)
            grammar_.add_transition(nt_sym, find_symbol(*j));
          ++cur_idx;
        }

        // Get parikh image of grammar.
        parikh_map_t parikh_image = grammar_.parikh_image();

        // Initialize positive and negative semilinear sets for elements on
        // rhs.
        vector<semilinear_set> pos;
        pos.reserve(rhs_states_.size());
        vector<semilinear_set> neg;
        neg.reserve(rhs_states_.size());
        { 
          typedef set<state_t>::const_iterator state_iter;
          state_iter end = rhs_states_.end();
          for (state_iter i = rhs_states_.begin(); i != end; ++i) {
            const symbol_t& sym = find_symbol(*i);
            pos.push_back(parikh_image.find(sym)->second);
            neg.push_back(complement(pos.back()));
          }
        }

        size_t reachable_count = state_count(image_);
        if (reachable_count == 0)
          return;
        // Try all combinations of rhs states
        // stack maintains the semilinear set for each state offset by 1.
        vector<semilinear_set> stack;
        stack.reserve(rhs_states_.size() + 1);
        stack.push_back(min_size_set(reachable_count, 2));

        bool abort = false;
        set<state_t> states;
        // We maintain the invariants:
        // * stack.back().is_empty() == false
        set<state_t>::const_iterator cur_state = rhs_states_.begin();
        vector<semilinear_set>::const_iterator cur_pos = pos.begin();
        vector<semilinear_set>::const_iterator cur_neg = neg.begin();

        while (!abort) {
          // If we have assigned all states
          if (cur_state == rhs_states_.end()) {
            // Create term
            vector<term_t> subterms;
            {
              if (ceta::is_empty(stack.back()))
                sig_error("Stack is empty");
                
              const linear_set_group& g = *stack.back().begin();
              const vector<unsigned>& constant = *g.constants().begin();

              for (size_t i = 0; i != constant.size(); ++i) {
                const term_t& subterm = (image_.begin() + i)->first;
                subterms.reserve(subterms.size() + constant[i]);
                for (size_t c = 0; c != constant[i]; ++c)
                  subterms.push_back(subterm);
              }
            }
            term_t term(op_, subterms.begin(), subterms.end());
            reachable_states_->add(term, states);

            // Increment and backtrack to next valid state
            bool backtracking = !abort;
            while ((cur_state != rhs_states_.begin()) && backtracking) {
              stack.pop_back();
              --cur_state;
              --cur_pos;
              --cur_neg;
              if (states.count(*cur_state) > 0) {
                states.erase(*cur_state);
                semilinear_set next = intersect(stack.back(), *cur_neg);
                if (!is_empty(next)) {
                  backtracking = false;
                  stack.push_back(next);
                  ++cur_state;
                  ++cur_pos;
                  ++cur_neg;
                }
              }
            }
            // If backtracking is still true, we are done
            if (backtracking)
              abort = true;
          } else {
            semilinear_set next = intersect(stack.back(), *cur_pos);
            if (!ceta::is_empty(next)) {
              // Branch to true case
              states.insert(*cur_state);
              stack.push_back(next);
            } else {
              // branch to false case
              stack.push_back(intersect(stack.back(), *cur_neg));
            }
            ++cur_state;
            ++cur_pos;
            ++cur_neg;
          }
        }
      }
    private:
      typedef map<state_t, symbol_t> nonterminal_map_t;

      /** Adds each state in s to grammar. */
      void add_states_to_grammar(const set<state_t>& s) {
        typedef set<state_t>::const_iterator state_iter;
        for (state_iter i = s.begin(); i != s.end(); ++i) {
          if (nonterminal_map_.count(*i) == 0) {
            symbol_t sym = grammar_.add_nonterminal(name(*i).c_str());
            nonterminal_map_.insert(make_pair(*i, sym));
          }
        }
      }

      /** 
       * Returns nonterminal symbol associated with state or throws error
       * if there is not one.
       */
      const symbol_t& find_symbol(const state_t& state) {
        nonterminal_map_t::const_iterator i = nonterminal_map_.find(state);
        if (i != nonterminal_map_.end()) {
          return i->second;
        } else {
          sig_error("Could not find state " + name(state) 
                  + " in nonterminal map.");
        }
      }

      /** 
       * The number of state sets in reachable_states_ that we have
       * processed.
       */
      size_t processed_count_;
      /** 
       * The reachable states intersected with the states that appear on
       * the left-hand-side of rule for operator.
       */
      reachable_image_t image_;
      /** States that appear on rhs of rule for op. */
      set<state_t> rhs_states_;
      /** Context free grammar built for rules of AC_explorer. */
      cfg_t grammar_;
      /** Mapping from states to symbol for that state. */
      nonterminal_map_t nonterminal_map_;
    };

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
    o << op(term);
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

  const theory_t::op_iterator
          add_op(theory_t& theory, const op_t& op) {
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
    return apply_visitor(state_models_visitor(model), pred);
  }
  ostream& operator<<(ostream& o, const state_predicate_t& p) {
    apply_visitor(print_visitor(&o), p);
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
  
  typedef map<op_t, vector<rule_t> > rule_partition_t;

  /** Partitions rules in automaton based on operator on left-hand-side. */
  static inline
  void add_rule_to_partition(const rule_t& rule, rule_partition_t& rules) {
    rules[op(rule)].push_back(rule);
  }

  static inline
  void add_erule_to_closure(const erule_t& rule,
                            epsilon_closure_t& closure) {
    add(closure, rule);
  }

  /**
   * Adds rules to closure by examining theory.  Rules on constant symbols
   * are added directly.  Guarded rules are added for binary symbols with 
   * identity.  Other rules are ignored.
   */
  static inline
  void add_rule_to_closure(const theory_t& theory, const rule_t& rule,
                           epsilon_closure_t& closure) {
    if (is_constant(op(rule))) {
      add(closure, make_pair(op(rule), rhs(rule)));
    } else if (is_binary(op(rule))) {
      axiom_set_t op_axioms = axioms(theory, op(rule));
      const state_t& lhs1 = lhs_state(rule, 0);
      const state_t& lhs2 = lhs_state(rule, 1);
      boost::optional<op_t> id = id_symbol(op_axioms);
      switch (id_type(op_axioms)) {
      case id_none:
        break;
      case id_left:
        add_guarded(closure, idrule_t(*id, lhs1), erule_t(lhs2, rhs(rule)));
        break;
      case id_right:
        add_guarded(closure, idrule_t(*id, lhs2), erule_t(lhs1, rhs(rule)));
        break;
      case id_both:
        add_guarded(closure, idrule_t(*id, lhs1), erule_t(lhs2, rhs(rule)));
        add_guarded(closure, idrule_t(*id, lhs2), erule_t(lhs1, rhs(rule)));
        break;
      }
    }
  }

  typedef list<boost::shared_ptr<op_explorer> > explorer_list_t;

  op_explorer* new_explorer(const ta_t& ta,
                            const epsilon_closure_t& closure,
                            const op_t& op,
                            const vector<rule_t>& rules,
                            reachable_states_t& states) {
    axiom_set_t cur_axioms = axioms(theory(ta), op);
    if (is_assoc(cur_axioms)) {
      if (is_comm(cur_axioms)) {
        return new    AC_explorer(theory(ta), closure, op, rules, states);
      } else {
        return new assoc_explorer(theory(ta), closure, op, rules, states);
      }
    } else {
      if (is_comm(cur_axioms)) {
        return new  comm_explorer(theory(ta), closure, op, rules, states);
      } else {
        return new  free_explorer(theory(ta), closure, op, rules, states);
      }
    }
  }
  
  const test_result_t test_emptiness(const ta_t& ta) {
    epsilon_closure_t closure;
    // Add each epsilon rule to closure
    for_each(erules_begin(ta), erules_end(ta),
             boost::bind(add_erule_to_closure,
                         _1,
                         boost::ref(closure)));
    // Add each rule to closure if needed.
    for_each(rules_begin(ta), rules_end(ta),
             boost::bind(add_rule_to_closure,
                         boost::cref(theory(ta)),
                         _1,
                         boost::ref(closure)));

    rule_partition_t rule_partition;
    // Add each rule to partition
    for_each(rules_begin(ta), rules_end(ta),
             boost::bind(add_rule_to_partition, 
                         _1,
                         boost::ref(rule_partition)));

    // Keep exploring until we stop finding new states.
    try {
      reachable_states_t reachable_states(ta);

      // Initialize explorers and reachable_states
      explorer_list_t explorers;
      typedef theory_t::op_iterator op_iter;
      op_iter end = ops_end(theory(ta));
      for (op_iter i = ops_begin(theory(ta)); i != end; ++i) {
        if (is_constant(*i)) {
          reachable_states.add(make_constant(*i), reachables(closure, *i));
        } else {
          explorers.push_back(
              boost::shared_ptr<op_explorer>(
                  new_explorer(ta, closure, *i, rule_partition[*i],
                               reachable_states)));
        }
      }
    
      bool found_new = true;
      while (found_new) {
        found_new = false;
        typedef explorer_list_t::iterator op_iter;
        for (op_iter i = explorers.begin(); i != explorers.end(); ++i) {
          kind_t k = output((*i)->op());
          size_t old_count = state_count(reachable_states, k);
          (*i)->explore();
          size_t new_count = state_count(reachable_states, k);
          found_new |= (old_count != new_count);
        }
      }
    } catch (const test_result_t& counterexample) {
      return counterexample;
    }
    return test_result_t();
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

  ostream& operator<<(ostream& o, const theory_t& theory) {
    decl_writer writer(&o);
    for_each(kinds_begin(theory), kinds_end(theory), writer);
    for_each(  ops_begin(theory),   ops_end(theory), writer);
    return o;
  }

  ostream& operator<<(ostream& o, const ta_t& ta) {
    o << theory(ta);
    decl_writer writer(&o);
    theory_t::kind_iterator k_begin = kinds_begin(theory(ta));
    theory_t::kind_iterator k_end   =   kinds_end(theory(ta));
    for (theory_t::kind_iterator i = k_begin; i != k_end; ++i)
      writer(predicate(ta, *i));
    for_each(erules_begin(ta), erules_end(ta), writer);
    for_each( rules_begin(ta),  rules_end(ta), writer);
    return o;
  }
}
