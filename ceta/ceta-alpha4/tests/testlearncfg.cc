#include "learncfg.hh"
#include "writer.hh"

#include <iostream>
#include <stdexcept>
#include <string>

using namespace ceta;
using namespace cfg;
using namespace std;

void error(const string& msg) {
  cerr << msg << endl;
  *(static_cast<int*>(NULL)) = 1;
  throw logic_error(msg);
}

void test_simple(void) {
  chomsky_rules_t<string> rules;
  rules.add_nonterminal("qa");
  rules.add_nonterminal("qb");
  rules.add_nonterminal("qboth");
  rules.add_rule("qa", "qa", "qa");
  rules.add_rule("qb", "qb", "qb");
  rules.add_rule("qboth", "qa", "qb");
  rules.add_rule("qboth", "qb", "qa");
  rules.add_rule("qboth", "qa", "qboth");
  rules.add_rule("qboth", "qboth", "qa");
  rules.add_rule("qboth", "qboth", "qb");
  rules.add_rule("qboth", "qb", "qboth");

  cfg_explorer_t<char, string> explorer(rules);

  // Expected states
  string states[] = { "qa", "qboth", "qb"};

  explorer.add_terminal('a', states, states + 1);
  explorer.add_terminal('b', states + 2, states + 3);

  // Number of reachables so far.
  size_t count = 0;
  while (!explorer.complete()) {
    explorer.work();
    if (explorer.has_reachable()) {
      const std::set<string>& r = explorer.reachable();

      if (count == 3)
        error("Too many reachable sets.");

      if (r.size() != 1)
        error("Too many elements.");

      const string& state = *r.begin();
      if (state != states[count])
        error("Unexpected element.");
      ++count;
      explorer.pop_reachable();
    }
  }
}

/**
 * Checks that explorer returns string 'aa' even though it has same reachable
 * states as 'a'
 */
void test_learn1() {
  chomsky_rules_t<string> rules;
  rules.add_nonterminal("qa");
  rules.add_rule("qa", "qa", "qa");

  string states[] = { "qa"};

  cfg_explorer_t<char, string> explorer(rules);
  explorer.add_terminal('a', states, states + 1);

  size_t found_count = 0;
  while (!explorer.complete()) {
    cerr << "Working" << endl;
    explorer.work();
    while (explorer.has_reachable()) {
      ++found_count;
      explorer.pop_reachable();
    }
  }

  if (found_count != 1)
    error("Unexpected number of state sets returned.");
}

int main(int argc, char **argv) {
  try {
    test_simple();
    test_learn1();
    return 0;
  } catch (const exception& e) {
    cerr << e.what() << endl;
    return 1;
  }
}
