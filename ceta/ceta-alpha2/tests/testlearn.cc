
#include "learn.hh"
#include "fa.hh"

#include <list>
#include <stdexcept>

#include <boost/assign/list_of.hpp>

#include <iostream>

using namespace std;
using namespace ceta;
using namespace ceta::fa;
using boost::assign::list_of;

void error(const string& msg) {
  cerr << msg << endl;
  *(static_cast<int*>(NULL)) = 1;
  throw logic_error(msg);
}

size_t accept_query_count = 0;
size_t advance_count = 0;

template<typename Symbol, typename State>
class dfa_state_t {
public:
  template<typename StateIterator>
  dfa_state_t(const rule_set_t<Symbol, State>* rules,
              const std::set<State>* accepting_states,
              StateIterator states_begin, StateIterator states_end)
    : rules_(rules),
      accepting_states_(accepting_states),
      subset_(states_begin, states_end) {
  }

  bool accept(void) const {
    ++accept_query_count;

    typedef typename std::set<State>::const_iterator iter;
    iter set_end = subset_.states().end();
    for (iter i = subset_.states().begin(); i != set_end; ++i) {
      if (accepting_states_->count(*i) > 0)
        return true;
    }
    return false;
  }
  void advance(const Symbol& sym) {
    ++advance_count;
    
    std::set<State> next = rules_->next_states(subset_.states(), sym);
    subset_
          = subset_t<Symbol, State>(subset_, sym, next.begin(), next.end());
  }
private:
  /** Pointer to rules for finite automaton. */
  const rule_set_t<Symbol, State>* rules_;
  /** Pointer to accepting states for dfa state. */
  const std::set<State>* accepting_states_;
    
  subset_t<Symbol, State> subset_;
};

template<typename State, typename TraceIterator, typename OutputIterator>
void write_states(const State& initial, 
                  TraceIterator trace_begin, TraceIterator trace_end,
                  OutputIterator& o) {
  State cur_state = initial;
  TraceIterator i = trace_begin;
  while (i != trace_end) {
    cerr << "Writing" << endl;
    cur_state.advance(*i);
    *o = cur_state;
    ++i; ++o;
  }
}

template<typename Alphabet, typename State, typename TraceIterator>
bool classifier_accept(const classifier_t<Alphabet, State>& c,
                       TraceIterator trace_begin,
                       TraceIterator trace_end) {
  const State* cur_rep = c.initial();
  for (TraceIterator i = trace_begin; i != trace_end; ++i) {
    State rep_copy = *cur_rep;
    rep_copy.advance(*i);
    cur_rep = c.classify(rep_copy);
  }
  return cur_rep->accept();
}

/**
 * Checks that learning algorithm correctly recognizes the DFA of an 
 * automaton that checks if the 4th most previous symbol was 'a'.  This
 * results in a minimum DFA with 2^4 = 16 states.
 */
void test_memory() {
  rule_set_t<char, size_t> rules;
  rules.add(0, 'a', 0);
  rules.add(0, 'b', 0);
  rules.add(0, 'a', 1);
  for (size_t i = 1; i != 4; ++i) {
    rules.add(i, 'a', i+1);
    rules.add(i, 'b', i+1);
  }
  typedef dfa_state_t<char, size_t> state_set_t;
  std::set<size_t> accepting;
  accepting.insert(4);
  size_t init_states[] = {0};
  std::vector<state_set_t> states;
  states.push_back(
          state_set_t(&rules, &accepting, init_states, init_states + 1));
  classifier_t<char, state_set_t> c(states[0]);
  string trace = "aaaa";

  //: Populate states with trace.
  back_insert_iterator< vector<state_set_t> > ii(states);
  write_states(states[0], trace.begin(), trace.end(), ii);

  accept_query_count = 0;
  advance_count = 0;

  // Analyze string
  if (classifier_accept(c, trace.begin(), trace.end())) 
    error("Classifier should not accept.");

  c.analyze(states.begin(), states.end(), trace.begin());
  if (classifier_accept(c, trace.begin(), trace.end())) 
    error("Did not expect classifier to accept so soon.");
  c.analyze(states.begin(), states.end(), trace.begin());
  c.analyze(states.begin(), states.end(), trace.begin());
  c.analyze(states.begin(), states.end(), trace.begin());
  if (!classifier_accept(c, trace.begin(), trace.end())) 
    error("Classifier should accept.");

  cerr << "Accept query count: " << accept_query_count
       << " Advance count: " << advance_count
       << endl;
}


int main(int argc, char **argv) {
  try {
    test_memory();
    return 0;
  } catch (const exception& e) {
    cerr << e.what() << endl;
    return 1;
  }
}
