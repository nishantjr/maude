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
 * Implementation for tree automata subset construction operations.
 */
#include "subset_construction.hh"

#include <list>

#include "closure.hh"
#include "learncfg.hh"
#include "parikh.hh"

using namespace std;
using namespace ceta::closure;
using namespace ceta::cfg;

namespace ceta {
  namespace impl {
    /**
     * Stores the reachable states intersected with the a subset of the
     * states.
     */
    class reachable_image_t {
    public:
      typedef vector< pair< term_t, set<state_t> > > set_vector_t;
      typedef set_vector_t::const_iterator iterator;

      reachable_image_t(const set<state_t>& allowed_states)
        : allowed_states_(allowed_states) {
      }

      void add(const pair< term_t, set<state_t> >& new_pair) {
        add(new_pair.first, new_pair.second);
      }

      bool add(const term_t& term, const set<state_t>& states) {
        // Compute intersection of set and allowed_states.
        set<state_t> subset;
        std::set_intersection(
                allowed_states_.begin(), allowed_states_.end(),
                states.begin(), states.end(),
                std::inserter(subset, subset.begin()));
        bool result = set_image_.insert(subset).second;
        if (result)
          set_vector_.push_back(make_pair(term, subset));
        return result;
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

    /**
     * Returns number of state sets added to image.
     * \relates reachable_image_t
     */
    size_t state_count(const reachable_image_t& image) {
      return std::distance(image.begin(), image.end());
    }

    /**
     * Returns last term and set added to image.
     * \relates reachable_image_t
     */
    const std::pair<term_t, std::set<state_t> >&
    back(const reachable_image_t& image) {
      reachable_image_t::iterator i = image.end(); --i;
      return *i;
    }

    /** Abstract base reachable set explorer for an operator. */
    class op_explorer_t {
    public:
      virtual ~op_explorer_t() {
      }

      /** Adds reachable state to op explorer. */
      virtual
      void add_reachable(const term_t& term,
                         const std::set<state_t>& set) = 0;

      /** Explore from current states. */
      virtual void explore(void) = 0;

      /** Returns true if this explorer has completely explored states. */
      virtual bool is_complete(void) const = 0;

      /** Returns true if this explorer has a new reachable state. */
      virtual bool has_next(void) const = 0;

      /** Returns next reachable set of states found. */
      virtual const std::set<state_t>& next_set(void) const = 0;

      /** Returns next reachable term found. */
      virtual const term_t next_term(void) const = 0;

      /** Pop next reachable pair from queue. */
      virtual void pop_next(void) = 0;
    };

    /**
     * Returns true if root of term is identity symbol in axioms for the
     * given position.
     */
    static
    bool is_identity(const term_t& term, const axiom_set_t& axioms,
                     size_t pos = 0) {
      switch (id_type(axioms)) {
      case id_none:
        return false;
      case id_left:
        return (pos == 1) && (*id_symbol(axioms) == root(term));
      case id_right:
        return (pos == 2) && (*id_symbol(axioms) == root(term));
      case id_both:
        return (*id_symbol(axioms) == root(term));
      default:
        throw std::logic_error("Unexpected identity type.");
      }
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

    /** Pair containing term and set of states it reaches. */
    typedef std::pair<term_t, std::set<state_t> > reachable_t;

    typedef epsilon_closure_t<op_t, state_t> eclosure_t;
    typedef boost::shared_ptr<eclosure_t> eclosure_ptr;

    /** Reachable set explorer for a free operator. */
    class free_explorer : public op_explorer_t {
    public:
      /** Constructs a new free explorer. */
      free_explorer(const op_t& op,
                    const axiom_set_t& axioms,
                    const eclosure_ptr& closure,
                    const vector<rule_t>& rules)
        : op_(op),
          axioms_(axioms),
          closure_(closure),
          rules_(rules),
          complete_(true),
          processed_counts_(input_count(op), 0) {
        op_t::input_iterator end = inputs_end(op);
        reachable_images_.reserve(input_count(op));
        for (op_t::input_iterator i = inputs_begin(op); i != end; ++i) {
          size_t cur_idx = reachable_images_.size();
          reachable_images_.push_back(reachable_image_t(
                  lhs_states(rules_.begin(), rules_.end(), cur_idx)));
        }
      }

      void add_reachable(const term_t& term,
                         const std::set<state_t>& set) {
        for (size_t i = 0; i != input_count(op_); ++i) {
          // Add term and set if kind matches and term is not identity.
          if ((kind(term) == input(op_, i))
                && !is_identity(term, axioms_, i)) {
            if (reachable_images_[i].add(term, set))
              complete_ = false;
          }
        }
      }

      void explore() {
        typedef reachable_image_t::iterator image_iter;
        // Range for each input.
        vector< incremental_range<image_iter> > ranges;
        ranges.reserve(input_count(op_));
        // Construct each range.
        for (size_t i = 0; i != input_count(op_); ++i) {
          const reachable_image_t& image = reachable_images_[i];
          size_t old_size = processed_counts_[i];
          // Add range for input
          ranges.push_back(incremental_range<image_iter>(
                     image.begin(), image.begin() + old_size, image.end()));
        }
        // Explore all new combinations
        new_combinations(ranges.begin(), ranges.end(), *this);
        // Update processed counts
        for (size_t i = 0; i != input_count(op_); ++i) {
          const reachable_image_t& image = reachable_images_[i];
          processed_counts_[i] = state_count(image);
        }
        complete_ = true;
      }

      /** Returns true if this explorer has completely explored states. */
      virtual bool is_complete(void) const {
        return complete_;
      }

      /** Returns true if this explorer has a new reachable state. */
      bool has_next(void) const {
        return !pending_.empty();
      }

      /** Returns next reachable term found. */
      const term_t next_term(void) const {
        return pending_.front().first;
      }

      /** Returns next reachable set of states found. */
      const std::set<state_t>& next_set(void) const {
        return pending_.front().second;
      }

      /** Pop next reachable pair from queue. */
      void pop_next(void) {
        pending_.pop_front();
      }

      /** Add reachable states for inputs to reachables_states_ */
      void operator()(const vector<reachable_image_t::iterator>& inputs) {
        set<state_t> states;
        typedef vector<rule_t>::const_iterator rule_iter;
        for (rule_iter i = rules_.begin(); i != rules_.end(); ++i) {
          if (lhs_in_inputs(*i, inputs)) {
            const set<state_t>& new_set = closure_->reachables(rhs(*i));
            states.insert(new_set.begin(), new_set.end());
          }
        }
        vector<term_t> subterms;
        subterms.reserve(inputs.size());
        typedef vector<reachable_image_t::iterator>::const_iterator
                input_iter;
        for (input_iter i = inputs.begin(); i != inputs.end(); ++i)
          subterms.push_back((*i)->first);
        term_t term(op_, subterms.begin(), subterms.end());
        pending_.push_back(reachable_t(term, states));
      }
    private:
      /**
       * Returns true if each state in the left-hand-side of the rule is in
       * the set of reachable states for the corresponding input.
       */
      bool lhs_in_inputs(const rule_t& rule,
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

      /** Operator for explorer. */
      const op_t op_;
      /** Axioms for operator. */
      const axiom_set_t axioms_;
      /** Epsilon closure for automaton. */
      const eclosure_ptr closure_;
      /** Rules for operator. */
      const vector<rule_t> rules_;
      /**
       * The reachable states for each input intersected with the states
       * that are used by that input.
       */
      vector<reachable_image_t> reachable_images_;
      /** Indicates if explorer is complete. */
      bool complete_;
      /** The number of state sets in each image that have been processed. */
      vector<size_t> processed_counts_;
      /** Queue of reachable states that have not been returned. */
      std::deque<reachable_t> pending_;
    };

    /** Reachable set explorer for a commutative operator. */
    class comm_explorer : public op_explorer_t {
    public:
      comm_explorer(const op_t& op,
                    const axiom_set_t& axioms,
                    const eclosure_ptr& closure,
                    const vector<rule_t>& rules)
        : op_(op),
          axioms_(axioms),
          closure_(closure),
          rules_(rules),
          image_(lhs_states(rules.begin(), rules.end())),
          processed_count_(0) {
      }

      void add_reachable(const term_t& term,
                         const std::set<state_t>& set) {
        // Add term and set if kind matches and term is not identity.
        if ((kind(term) == output(op_) ) && !is_identity(term, axioms_))
          image_.add(term, set);
      }

      void explore(void) {
        typedef reachable_image_t::iterator image_iter;
        kind_t k = output(op_);
        // Explore all new combinations
        image_iter img_begin     = image_.begin();
        image_iter img_new_begin = image_.begin() + processed_count_;
        image_iter img_end       = image_.end();
        // For each new state in image
        for (image_iter i = img_new_begin; i != img_end; ++i) {
          // For every state added before i.
          for (image_iter j = img_begin; j != i + 1; ++j) {
            explore(*i, *j);
          }
        }
        // Update processed counts
        processed_count_ = state_count(image_);
      }

      /** Returns true if this explorer has completely explored states. */
      virtual bool is_complete(void) const {
        return (processed_count_ == state_count(image_));
      }

      /** Returns true if this explorer has a new reachable set. */
      bool has_next(void) const {
        return !pending_.empty();
      }

      /** Returns next reachable term found. */
      const term_t next_term(void) const {
        return pending_.front().first;
      }

      /** Returns next reachable set of states found. */
      const std::set<state_t>& next_set(void) const {
        return pending_.front().second;
      }

      /** Pop next reachable pair from queue. */
      void pop_next(void) {
        pending_.pop_front();
      }
    private:
      /** Add reachable pair from x and y to reachable states. */
      void explore(const reachable_t& x, const reachable_t& y) {
        set<state_t> states;
        typedef vector<rule_t>::const_iterator rule_iter;
        for (rule_iter i = rules_.begin(); i != rules_.end(); ++i) {
          if (lhs_in_inputs(*i, x.second, y.second)) {
            const set<state_t>& new_set = closure_->reachables(rhs(*i));
            states.insert(new_set.begin(), new_set.end());
          }
        }
        const term_t subterms[] = { x.first, y.first };
        term_t term(op_, subterms, subterms + 2);
        pending_.push_back(reachable_t(term, states));
      }

      /**
       * Returns true if the states in the left-hand side of the rule
       * belongs to the set of reachable states in the inputs or can
       * be permuted to do so.
       */
      bool lhs_in_inputs(const rule_t& rule, const set<state_t>& x,
                         const set<state_t>& y) {
        const state_t& lhs0 = lhs_state(rule, 0);
        const state_t& lhs1 = lhs_state(rule, 1);
        return (x.count(lhs0) > 0) && (y.count(lhs1) > 0)
            || (x.count(lhs1) > 0) && (y.count(lhs0) > 0);
      }

      /** Operator for explorer. */
      const op_t op_;
      /** Axioms for operator. */
      const axiom_set_t axioms_;
      /** Epsilon closure for automaton. */
      const eclosure_ptr closure_;
      /** Rules for operator. */
      const vector<rule_t> rules_;
      /**
       * The reachable states intersected with the states that appear on
       * the left-hand-side of rule for operator.
       */
      reachable_image_t image_;
      /** Number of state sets in image_ that we have explored. */
      size_t processed_count_;
      /** Queue of reachable states that have not been returned. */
      std::deque<reachable_t> pending_;
    };

    /** Reachable set explorer for an associative operator. */
    class assoc_explorer : public op_explorer_t {
    public:
      assoc_explorer(const op_t& op,
                     const axiom_set_t& axioms,
                     const eclosure_ptr& closure,
                     const vector<rule_t>& rules)
        : op_(op),
          axioms_(axioms),
          image_(lhs_states(rules.begin(), rules.end())),
          explorer_(make_explorer(closure, rules)) {
      }

      /** Add reachable term and set to explorer. */
      void add_reachable(const term_t& term, const std::set<state_t>& set) {
        if ((kind(term) == output(op_))
                && (root(term) != op_)
                && !is_identity(term, axioms_)) {
          bool added = image_.add(term, set);
          if (added) {
            const std::set<state_t>& nset = back(image_).second;
            size_t last_index = state_count(image_) - 1;
            explorer_.add_terminal(last_index, nset.begin(), nset.end());
          }
        }
      }

      void explore() {
        // Maximum number of times to call work when exploring.
        const size_t max_work_count = 40;
        size_t i = 0;
        while (!explorer_.complete()
            && !explorer_.has_reachable()
            && (i < max_work_count)) {
          explorer_.work();
          ++i;
        }
      }

      /** Returns true if this explorer has completely explored states. */
      virtual bool is_complete(void) const {
        return explorer_.complete();
      }

      /** Returns true if this explorer has a new reachable state. */
      bool has_next(void) const {
        return explorer_.has_reachable();
      }

      /** Returns next reachable term found. */
      const term_t next_term(void) const {
        const std::vector<size_t>& next_string = explorer_.string();

        std::vector<term_t> subterms;
        subterms.reserve(next_string.size());
        // Build term from string.
        typedef std::vector<size_t>::const_iterator iter;
        for (iter i = next_string.begin(); i != next_string.end(); ++i) {
          const term_t& term = (image_.begin() + *i)->first;
          subterms.push_back(term);
        }
        return term_t(op_, subterms.begin(), subterms.end());
      }

      /** Returns next reachable set of states found. */
      const std::set<state_t>& next_set(void) const {
        return explorer_.reachable();
      }

      /** Pop next reachable pair from queue. */
      void pop_next(void) {
        explorer_.pop_reachable();
      }
    private:
      /**
       * Constructs a CFG explorer from the given epsilon closure and rules.
       */
      static
      const cfg_explorer_t<size_t, state_t>
      make_explorer(const eclosure_ptr& closure,
                    const vector<rule_t>& rules) {
        // Set of states found in rule or closure of rhs.
        std::set<state_t> states;
        std::vector< cfg_rule_t<state_t> > cfg_rules;
        typedef std::vector<rule_t>::const_iterator rule_iter;
        for (rule_iter i = rules.begin(); i != rules.end(); ++i) {
          state_t first_state  = lhs_state(*i, 0);
          states.insert( first_state);
          state_t second_state = lhs_state(*i, 1);
          states.insert(second_state);
          const std::set<state_t> rhs_set = closure->reachables(rhs(*i));
          typedef std::set<state_t>::const_iterator state_iter;
          for (state_iter j = rhs_set.begin(); j != rhs_set.end(); ++j) {
            states.insert(*j);
            cfg_rules.push_back(
                    cfg_rule_t<state_t>(*j, first_state, second_state));
          }
        }
        return cfg_explorer_t<size_t, state_t>(states.begin(), states.end(),
                cfg_rules.begin(), cfg_rules.end());
      }

      /** Operator for explorer. */
      const op_t op_;
      /** Axioms for operator. */
      const axiom_set_t axioms_;
      /** Reachable states that are terminals in the explorer. */
      reachable_image_t image_;
      /** Underlying CFG explorer. */
      cfg_explorer_t<size_t, state_t> explorer_;
    };

    /**
     * Reachable set explorer for an associative and commutative operator.
     */
    class AC_explorer : public op_explorer_t {
    public:
      /** Constructs a new AC explorer. */
      AC_explorer(const op_t& op,
                  const axiom_set_t& axioms,
                  const eclosure_ptr& closure,
                  const vector<rule_t>& rules)
        : op_(op),
          axioms_(axioms),
          closure_(closure),
          complete_(true),
          image_(lhs_states(rules.begin(), rules.end())),
          processed_count_(0),
          rhs_states_(rhs_states(rules.begin(), rules.end())) {

        set<state_t> states = image_.states();
        states.insert(rhs_states_.begin(), rhs_states_.end());

        // Add epsilon rules to grammar.
        typedef set<state_t>::const_iterator state_iter;
        state_iter s_begin = states.begin();
        state_iter s_end = states.end();
        for (state_iter i = s_begin; i != s_end; ++i) {
          grammar_.add_nonterminal(*i);
        }
        for (state_iter i = s_begin; i != s_end; ++i) {
          for (state_iter j = s_begin; j != s_end; ++j) {
            if ((i != j) && closure->is_reachable(*i, *j)) {
              grammar_.add(*j, *i);
            }
          }
        }

        // Add regular rules to grammar.
        typedef vector<rule_t>::const_iterator rule_iter;
        for (rule_iter i = rules.begin(); i != rules.end(); ++i) {
          // Add *i to grammar
          grammar_.add(
                  make_rrule(rhs(*i), lhs_state(*i, 0), lhs_state(*i, 1)));
        }
      }

      void add_reachable(const term_t& term, const std::set<state_t>& set) {
        if ((kind(term) == output(op_))
                && (root(term) != op_)
                && !is_identity(term, axioms_)) {
          image_.add(term, set);
        }
      }

      /**
       * Explore new reachable states.  Note that if this operation throws
       * an exception, the explorer will become unusable.
       * TODO: Adding guiding to exploration so that:
       * * We do not explore routes that are guaranteed to reach states we
       *   already know are reachable.
       * * The exploration route will hit at least one semilinear set that
       *   is larger than it was in a previous round.
       * * Intelligently chose ordering of variables to assign.
       */
      void explore() {
        kind_t k = output(op_);
        // Add new states in image to grammar.
        typedef reachable_image_t::iterator image_iter;
        image_iter img_begin = image_.begin() + processed_count_;
        image_iter img_end   = image_.end();
        for (image_iter i = img_begin; i != img_end; ++i) {
          grammar_.add_terminal(processed_count_);
          // Add production for each state in cur_set to cur_set to grammar.
          const set<state_t>& cur_set = i->second;
          typedef set<state_t>::const_iterator state_iter;
          state_iter set_end = cur_set.end();
          for (state_iter j = cur_set.begin(); j != set_end; ++j)
            grammar_.add(make_trule(*j, processed_count_));
          ++processed_count_;
        }

        // Get parikh image of grammar.
        typedef std::map<state_t, semilinear_set> pimage_t;
        pimage_t pimage = parikh_image(processed_count_, grammar_);

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
            pos.push_back(pimage.find(*i)->second);
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
                throw std::logic_error("Stack is empty");

              const linear_set_group& g = *stack.back().begin();
              const vector<unsigned>& constant = *g.constants().begin();

              for (size_t i = 0; i != constant.size(); ++i) {
                const term_t& subterm = (image_.begin() + i)->first;
                subterms.reserve(subterms.size() + constant[i]);
                for (size_t c = 0; c != constant[i]; ++c)
                  subterms.push_back(subterm);
              }
            }
            // Close states with respect to epsilon transitions.
            term_t term(op_, subterms.begin(), subterms.end());
            pending_.push_back(reachable_t(term,
                    closed_set(*closure_, states.begin(), states.end())));

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
        complete_ = true;
      }

      /** Returns true if this explorer has completely explored states. */
      virtual bool is_complete(void) const {
        return (processed_count_ == state_count(image_));
      }

      /** Returns true if this explorer has a new reachable state. */
      bool has_next(void) const {
        return !pending_.empty();
      }

      /** Returns next reachable term found. */
      const term_t next_term(void) const {
        return pending_.front().first;
      }

      /** Returns next reachable set of states found. */
      const std::set<state_t>& next_set(void) const {
        return pending_.front().second;
      }

      /** Pop next reachable pair from queue. */
      void pop_next(void) {
        pending_.pop_front();
      }
    private:
      typedef std::pair<term_t, std::set<state_t> > reachable_t;

      /** Operator for explorer. */
      const op_t op_;
      /** Axioms for operator. */
      const axiom_set_t axioms_;
      /** Epsilon closure for automaton. */
      const eclosure_ptr closure_;
      /** Context free grammar built for rules of AC_explorer. */
      cfg_t<size_t, state_t> grammar_;
      /** Indicates if explorer is complete. */
      bool complete_;
      /**
       * The reachable states intersected with the states that appear on
       * the left-hand-side of rule for operator.
       */
      reachable_image_t image_;
      /** Number of state sets in image_ that have been processed. */
      size_t processed_count_;
      /** States that appear on rhs of rule for op. */
      set<state_t> rhs_states_;
      /** Queue of reachable states that have not been returned. */
      std::deque<reachable_t> pending_;
    };

    typedef map<kind_t, state_predicate_t> predicate_map_t;
  }

  using namespace impl;

  /** Implementation of subset constructor algorithm. */
  class subset_constructor_impl {
  public:
    /** Constructs a new subset constructor implementation. */
    subset_constructor_impl(const ta_t& ta) {
      const theory_t& cur_theory = theory(ta);
      eclosure_ptr closure(new eclosure_t());
      // Add each epsilon rule to closure
      typedef ta_t::erule_iterator erule_iter;
      for (erule_iter i = erules_begin(ta); i != erules_end(ta); ++i)
        closure->add_erule(lhs(*i), rhs(*i));
      // Add each rule to closure if needed.
      typedef ta_t::rule_iterator rule_iter;
      for (rule_iter i = rules_begin(ta); i != rules_end(ta); ++i) {
        const rule_t& rule = *i;
        if (is_constant(op(rule))) {
          closure->add_rule(op(rule), rhs(rule));
        } else if (is_binary(op(rule))) {
          axiom_set_t op_axioms = axioms(cur_theory, op(rule));
          const state_t& lhs1 = lhs_state(rule, 0);
          const state_t& lhs2 = lhs_state(rule, 1);
          boost::optional<op_t> id = id_symbol(op_axioms);
          switch (id_type(op_axioms)) {
          case id_none:
            break;
          case id_left:
            closure->add_guarded(*id, lhs1, lhs2, rhs(rule));
            break;
          case id_right:
            closure->add_guarded(*id, lhs2, lhs1, rhs(rule));
            break;
          case id_both:
            closure->add_guarded(*id, lhs1, lhs2, rhs(rule));
            closure->add_guarded(*id, lhs2, lhs1, rhs(rule));
            break;
          }
        }
      }

      // Partition of rules in automaton based on operator on left-hand side.
      typedef map<op_t, vector<rule_t> > rule_partition_t;

      rule_partition_t rule_partition;
      // Add each rule to partition
      for (rule_iter i = rules_begin(ta); i != rules_end(ta); ++i)
        rule_partition[op(*i)].push_back(*i);

      std::vector<op_t> constants;
      typedef theory_t::op_iterator op_iter;
      op_iter end = ops_end(theory(ta));
      for (op_iter i = ops_begin(theory(ta)); i != end; ++i) {
        const op_t& op = *i;
        if (is_constant(op)) {
          constants.push_back(op);
        } else {
          axiom_set_t cur_axioms = axioms(cur_theory, op);
          const vector<rule_t>& rules = rule_partition[*i];
          explorer_ptr new_explorer
            = is_assoc(cur_axioms)
                ? (is_comm(cur_axioms)
                  ? explorer_ptr(
                      new AC_explorer(op, cur_axioms, closure, rules))
                  : explorer_ptr(
                      new assoc_explorer(op, cur_axioms, closure, rules)))
                : (is_comm(cur_axioms)
                  ? explorer_ptr(
                      new  comm_explorer(op, cur_axioms, closure, rules))
                  : explorer_ptr(
                      new  free_explorer(op, cur_axioms, closure, rules)));
          explorers_.push_back(new_explorer);
        }
      }
      // Add reachable set for each constant to explorers.
      typedef std::vector<op_t>::const_iterator const_iter;
      for (const_iter i = constants.begin(); i != constants.end(); ++i) {
        term_t term = make_constant(*i);
        std::set<state_t> set = closure->reachables(*i);
        add_reachable(term, set);
      }
    }

    /** Performs some finite amount of work in subset construction. */
    void work(void) {
      if (!active_.empty()) {
        op_explorer_t& cur_explorer = *active_.front();
        cur_explorer.explore();
        // Add any reachable states found.
        while (cur_explorer.has_next()) {
          const term_t term = cur_explorer.next_term();
          const std::set<state_t>& set = cur_explorer.next_set();
          add_reachable(term, set);
          cur_explorer.pop_next();
        }
        // Deactivate explorer if complete.
        if (cur_explorer.is_complete()) {
          active_.pop_front();
        }
      }
    }

    /** Returns true if subset construction has found all reachable sets. */
    bool is_complete(void) const {
      return active_.empty();
    }

    /** Returns true if constructor has a new reachable set. */
    bool has_next(void) const {
      return !queue_.empty();
    }

    /** Returns next reachable set. */
    const std::set<state_t>& next_set(void) const {
      return queue_.front().first;
    }

    /** Returns term for next reachable set. */
    const term_t& next_term(void) const {
      return queue_.front().second;
    }

    /** Pops next reachable set from queue. */
    void pop_next(void) {
      queue_.pop_front();
    }
  private:
    /** Disable copy constructor. */
    subset_constructor_impl(const subset_constructor_impl&);
    /** Disable assignment. */
    subset_constructor_impl& operator=(const subset_constructor_impl&);
    typedef boost::shared_ptr<op_explorer_t> explorer_ptr;

    /**
     * Add the term and states as a reachable to each explorer.
     * Also if the explorer was previously identified as
     * complete and is not after adding the reachable, add the explorer to
     * the active queue.
     */
    void add_reachable(const term_t& term,
                       const std::set<state_t>& states) {
      queue_.push_back(pending_pair_t(states, term));
      typedef explorer_list_t::iterator iter;
      for (iter i = explorers_.begin(); i != explorers_.end(); ++i) {
        boost::shared_ptr<op_explorer_t>& cur_explorer = *i;
        bool prev_complete = cur_explorer->is_complete();
        (*i)->add_reachable(term, states);
        // If i was previously complete and is not now.
        if (prev_complete && !cur_explorer->is_complete()) {
          active_.push_back(cur_explorer);
        }
      }
    }

    typedef std::pair<std::set<state_t>, term_t> pending_pair_t;

    typedef std::list<explorer_ptr> explorer_list_t;
    /** Queue of explorers that are active. */
    std::deque<explorer_ptr> active_;
    /** List of non-constant operator explorers. */
    explorer_list_t explorers_;
    /** Queue of pairs states and terms remaining to return. */
    std::deque<pending_pair_t> queue_;
  };

  subset_constructor_t::subset_constructor_t(const ta_t& ta)
    : impl_(new subset_constructor_impl(ta)) {
  }

  void subset_constructor_t::work(void) {
    impl_->work();
  }

  bool subset_constructor_t::is_complete(void) const {
    return impl_->is_complete();
  }

  bool subset_constructor_t::has_next(void) const {
    return impl_->has_next();
  }

  const std::set<state_t>& subset_constructor_t::next_set(void) const {
    return impl_->next_set();
  }

  const term_t& subset_constructor_t::next_term(void) const {
    return impl_->next_term();
  }

  void subset_constructor_t::pop_next(void) {
    return impl_->pop_next();
  }

}
