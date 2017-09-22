#include "earley.hh"

#include <iostream>
#include <list>
#include <stdexcept>

#include <boost/assign/list_of.hpp>

using namespace std;
using namespace ceta;
using namespace ceta::cfg;
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
  typedef std::set<string>::const_iterator set_iter;
  for (set_iter i = set.begin(); i != set.end(); ++i) {
    cerr << *i << " ";
  }
  cerr << endl;
  
  if (set.size() != expected.size())
    error("Size of set does not matched expected.");
  typedef std::list<string>::const_iterator iter;
  for (iter i = expected.begin(); i != expected.end(); ++i) {
    if (set.count(*i) == 0)
      error("Could not find expected string '" + *i + "' in set.");
  }
}

void test_simple() {
  // Create rules that should recognize strings of form a^n b^n (n >= 1)
  // with state "f".
  chomsky_rules_t<string> rules;
  rules.add_nonterminal("qa");
  rules.add_nonterminal("qb");
  rules.add_nonterminal("f");
  rules.add_nonterminal("pa");
  rules.add_rule("f", "qa", "qb");
  rules.add_rule("pa", "qa", "f");
  rules.add_rule("f", "pa", "qb");

  check_set(rules.searches("f"), list_of<string>("f")("pa")("qa"));
  check_set(rules.followups("f", "qa"), list_of<string>("qb"));

  terminal_rules_t<char, string> trules;
  string qa[] = {"qa"};
  string qb[] = {"qb"};
  trules.add_terminal('a', qa, qa + 1);
  trules.add_terminal('b', qb, qb + 1);
  check_set(trules.generators('a'), list_of<string>("qa"));
  check_set(trules.generators('b'), list_of<string>("qb"));

  string test = "aaabbb";
  if (!member(rules, trules, string("f"), test.begin(), test.end()))
    error("Incorrect parse 'aaabbb'");
  test = "aaabbbb";
  if (member(rules, trules, string("f"), test.begin(), test.end()))
    error("Incorrect parse 'aaabbbb'");
}


int main(int argc, char **argv)
{
  try {
    test_simple();
    return 0;
  } catch (const exception& e) {
    cerr << e.what() << endl;
    return 1;
  }
}
