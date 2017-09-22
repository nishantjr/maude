#include "ac_parser.hh"
#include <iostream>
#include <stdexcept>
#include <string>

void sig_error(const std::string& str) {
  std::cerr << str << std::endl;
  *static_cast<int*>(NULL) = 2;
}

std::ostream& operator<<(std::ostream& o, const std::set<std::string>& s) {
  typedef std::set<std::string>::const_iterator iter;
  for (iter i = s.begin(); i != s.end(); ++i) {
    o << *i << " ";
  }
  return o;
}


void test_acparser() {
  ceta::ac_parser_t<std::string> parser;
  parser.add_nonterminal("cBool");
  parser.add_nonterminal("dBool");
  parser.add_nonterminal("kBool");
  parser.add_nonterminal("rBool");
  parser.add_nonterminal("BoolTerm0");
  parser.add_nonterminal("BoolTerm1");
  parser.add_nonterminal("BoolTerm2");

  parser.add_rule("BoolTerm0", "cBool", "cBool");
  parser.add_rule("dBool", "cBool", "cBool");
  parser.add_rule("kBool", "kBool", "kBool");
  parser.add_rule("rBool", "BoolTerm1", "cBool");
  parser.add_rule("rBool", "BoolTerm2", "BoolTerm2");
  parser.add_rule("rBool", "kBool", "rBool");


  std::set<std::string> t_true;
  t_true.insert("BoolTerm2");
  t_true.insert("cBool");
  t_true.insert("kBool");


  std::set<std::string> t_false;
  t_false.insert("BoolTerm1");
  t_false.insert("cBool");
  t_false.insert("kBool");

  std::set<std::string> t_implies;
  t_implies.insert("kBool");
  t_implies.insert("rBool");

  std::map< std::set<std::string>, size_t> counts;
  counts[t_true] = 1;
  counts[t_implies] = 2;
  std::set<std::string> parse_result = parser.parse(counts);
  std::cerr << "result: " << parse_result << std::endl;

  std::set<std::string> expected_result;
  expected_result.insert("kBool");
  expected_result.insert("rBool");
  if (parse_result != expected_result)
    sig_error("Unexpected result");
}

int main(int argc, char **argv) {
  try {
    // Test number with natural numbers and multisets
    test_acparser();
    return 0;
  } catch (const std::exception& e) {
    std::cerr << e.what() << std::endl;
    return 1;
  }
}
