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
  std::vector<string> nonterminals;
  nonterminals.push_back("qa");
  nonterminals.push_back("qb");
  nonterminals.push_back("qboth");

  typedef cfg_rule_t<string> rule_t;
  std::vector<rule_t> rules;
  rules.push_back(rule_t("qa", "qa", "qa"));
  rules.push_back(rule_t("qb", "qb", "qb"));
  rules.push_back(rule_t("qboth", "qa", "qb"));
  rules.push_back(rule_t("qboth", "qb", "qa"));
  rules.push_back(rule_t("qboth", "qa", "qboth"));
  rules.push_back(rule_t("qboth", "qboth", "qa"));
  rules.push_back(rule_t("qboth", "qboth", "qb"));
  rules.push_back(rule_t("qboth", "qb", "qboth"));

  cfg_explorer_t<char, string>
    explorer(nonterminals.begin(), nonterminals.end(),
             rules.begin(), rules.end());
  explorer.add_terminal('a', &nonterminals[0], &nonterminals[0] + 1);
  explorer.add_terminal('b', &nonterminals[1], &nonterminals[1] + 1);

  // Expected states
  string states[] = { "qa", "qboth", "qb"};
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
  std::vector<string> nonterminals;
  nonterminals.push_back("qa");

  typedef cfg_rule_t<string> rule_t;
  std::vector<rule_t> rules;
  rules.push_back(rule_t("qa", "qa", "qa"));

  cfg_explorer_t<char, string>
    explorer(nonterminals.begin(), nonterminals.end(),
             rules.begin(), rules.end());
  explorer.add_terminal('a', &nonterminals[0], &nonterminals[0] + 1);

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
