#include "fa.hh"

#include <iostream>
#include <list>
#include <stdexcept>

#include <boost/assign/list_of.hpp>

using namespace std;
using namespace ceta;
using namespace ceta::fa;
using boost::assign::list_of;

void error(const string& msg) {
  cerr << msg << endl;
  *(static_cast<int*>(NULL)) = 1;
  throw logic_error(msg);
}

/**
 * Checks that every element in list is in set and that the size of list and
 * set are the same.
 */
void check_set(const std::set<string>& set,
               const std::list<string>& expected) {
  if (set.size() != expected.size())
    error("Size of set does not matched expected.");
  typedef std::list<string>::const_iterator iter;
  for (iter i = expected.begin(); i != expected.end(); ++i) {
    if (set.count(*i) == 0)
      error("Could not find expected string '" + *i + "' in set.");
  }
}

/**
 * Tests subset construction on an automaton that checks if the 4th most
 * previous symbol was 'a'.  This results in a minimum DFA with 2^4 = 16
 * states.
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
  char symbols[] = {'a', 'b'};
  int initial_states[] = {0};
  subset_constructor_t<char, size_t>
        c(rules,
          symbols, symbols + 2,
          initial_states, initial_states + 1);

  // Check that number of subsets constructed is as expected.
  size_t subset_count = 0;
  while (c.has_next()) {
    ++subset_count;
    c.pop_next();
  }
  if (subset_count != 16)
    error("Wrong number of subsets constructed.");
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
