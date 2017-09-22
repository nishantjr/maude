#include "membership.hh"
#include "closure.hh"
#include "earley.hh"
#include "ac_parser.hh"

namespace ceta {
class op_parser_t {
public:
  /** Constructs a new op parser. */
  op_parser_t(const term_t& term)
    : inext_(subterms_begin(term)),
      term_end_(subterms_end(term)) {
  }

  bool has_next(void) const {
    return inext_ != term_end_;
  }

  const term_t next_term(void) {
    term_t result = *inext_;
    ++inext_;
    return result;
  }

  /** Destroys parser. */
  virtual ~op_parser_t(void) {}
  /** Indicates complete set of states accepted by next_subterm. */
  virtual void record_states(const std::set<state_t>& states) = 0;
  /** Returns complete set of representative states accepted by op. */
  virtual const std::set<state_t> states(void) const = 0;
private:
  term_t::subterm_iterator inext_;
  term_t::subterm_iterator term_end_;
};

class free_op_parser_t : public op_parser_t {
public:
  free_op_parser_t(const closure_t& closure,
                   const term_t& term)
    : op_parser_t(term),
      closure_(closure),
      rules_(closure.op_rules(root(term))) {
  }

  void record_states(const std::set<state_t>& states) {
    state_vector_.push_back(states);
  }

  /** Returns complete set of representative states accepted by op. */
  const std::set<state_t> states(void) const {
    std::set<state_t> result;
    typedef rule_vector_t::const_iterator rule_iter;
    // Iterate through rules.
    for (rule_iter ir = rules_.begin(); ir != rules_.end(); ++ir) {
      if (lhs_in_states(*ir))
        closure_.add_and_close(result, rhs(*ir));
    }
    return result;
  }
private:
  /**
   * Returns true if every state in rule lhs is in corresponding
   * state_vector_ set.
   */
  bool lhs_in_states(const rule_t& rule) const {
    typedef std::vector<state_set_t>::const_iterator set_iter;
    typedef rule_t::lhs_state_iterator lhs_iter;
    lhs_iter lhs_begin = lhs_states_begin(rule);
    lhs_iter lhs_end = lhs_states_end(rule);
    set_iter is = state_vector_.begin();
    for (lhs_iter il = lhs_begin; il != lhs_end; ++il) {
      if (is->count(*il) == 0)
        return false;
      ++is;
    }
    return true;
  }

  const closure_t& closure_;
  typedef std::vector<rule_t> rule_vector_t;
  const rule_vector_t rules_;
  typedef std::set<state_t> state_set_t;
  std::vector<state_set_t> state_vector_;
};

class comm_op_parser_t : public op_parser_t {
public:
  comm_op_parser_t(const closure_t& closure, const term_t& term)
    : op_parser_t(term),
      closure_(closure),
      rules_(closure.op_rules(root(term))) {
  }

  void record_states(const std::set<state_t>& states) {
    state_vector_.push_back(states);
  }

  /** Returns complete set of representative states accepted by op. */
  const std::set<state_t> states(void) const {
    std::set<state_t> result;
    typedef rule_vector_t::const_iterator rule_iter;
    // Iterate through rules.
    for (rule_iter ir = rules_.begin(); ir != rules_.end(); ++ir) {
      if (lhs_in_states(*ir))
        closure_.add_and_close(result, rhs(*ir));
    }
    return result;
  }
private:
  /**
   * Returns true if every state in rule lhs is in corresponding
   * state_vector_ set.
   */
  bool lhs_in_states(const rule_t& rule) const {
    const state_set_t& first_set = state_vector_[0];
    const state_set_t& second_set = state_vector_[1];
    const state_t& first_lhs = lhs_state(rule, 0);
    const state_t second_lhs = lhs_state(rule, 1);
    return (first_set.count(first_lhs) && second_set.count(second_lhs))
        || (first_set.count(second_lhs) && second_set.count(first_lhs));
  }

  const closure_t& closure_;
  typedef std::vector<rule_t> rule_vector_t;
  const rule_vector_t rules_;
  typedef std::set<state_t> state_set_t;
  std::vector<state_set_t> state_vector_;
};

class assoc_op_parser_t : public op_parser_t {
public:
  assoc_op_parser_t(const ta_t& ta,
                    const closure_t& closure,
                    const term_t& term)
    : op_parser_t(term),
      rules_(make_rules<rules_t>(closure, root(term))),
      trace_(rules_) {
  }

  void record_states(const std::set<state_t>& states) {
    parse_result_ = parse(rules_, trace_, states.begin(), states.end());
  }

  const std::set<state_t> states(void) const {
    typedef parse_result_t::const_iterator iter;
    iter iend = parse_result_.end();
    std::set<state_t> result;
    for (iter i = parse_result_.begin(); i != iend; ++i) {
      if (i->set == trace_[0])
        result.insert(i->nt);
    }
    return result;
  }
private:
  typedef cfg::chomsky_rules_t<state_t> rules_t;
  rules_t rules_;
  cfg::earley_trace_t<state_t> trace_;
  typedef std::set< cfg::prefix_pair_t<state_t> > parse_result_t;
  parse_result_t parse_result_;
};

class ac_op_parser_t : public op_parser_t {
public:
  ac_op_parser_t(const ta_t& ta,
                 const closure_t& closure,
                 const term_t& term)
    : op_parser_t(term),
      parser_(make_rules<parser_t>(closure, root(term))) {
  }

  /** Record new reachable states by incrementing count. */
  void record_states(const std::set<state_t>& states) {
    typedef set_counts_t::iterator count_iter_t;
    count_iter_t ic = set_counts_.find(states);
    // If this set has been added, increment count.
    if (ic != set_counts_.end()) {
      ++(ic->second);
    } else {
      set_counts_[states] = 1;
    }
  }

  const std::set<state_t> states(void) const {
    return parser_.parse(set_counts_);
  }
private:
  typedef std::set<state_t> state_set_t;
  typedef std::map<state_set_t, size_t> set_counts_t;

  set_counts_t set_counts_;

  typedef ac_parser_t<state_t> parser_t;
  parser_t parser_;
};

/** Creates a new parser for the given term's root. */
op_parser_t* create_parser(const ta_t& ta,
                           const closure_t& closure,
                           const term_t& term) {
  const axiom_set_t& cur_axioms = axioms(theory(ta), root(term));
  if (is_assoc(cur_axioms)) {
    if (is_comm(cur_axioms)) {
      return new ac_op_parser_t(ta, closure, term);
    } else {
      return new assoc_op_parser_t(ta, closure, term);
    }
  } else {
    if (is_comm(cur_axioms)) {
      return new comm_op_parser_t(closure, term);
    } else {
      return new free_op_parser_t(closure, term);
    }
  }
}

const std::set<state_t>
reachable_states(const ta_t& ta, const term_t& term) {
  closure_t closure(ta);
  typedef boost::shared_ptr<op_parser_t> parser_ptr_t;
  std::vector<parser_ptr_t> parsers_;
  parsers_.push_back(parser_ptr_t(create_parser(theory(ta), closure, term)));
  std::set<state_t> result;
  while (!parsers_.empty()) {
    if (parsers_.back()->has_next()) {
      term_t term = parsers_.back()->next_term();
      parsers_.push_back(
              parser_ptr_t(create_parser(theory(ta), closure, term)));
    } else {
      result = parsers_.back()->states();
      parsers_.pop_back();
      if (!parsers_.empty())
        parsers_.back()->record_states(result);
    }
  }
  return closure.full_set(result);
}

bool test_membership(const ta_t& ta, const term_t& term) {
  return models(predicate(ta, kind(term)),
                reachable_states(ta, term));
}
}
