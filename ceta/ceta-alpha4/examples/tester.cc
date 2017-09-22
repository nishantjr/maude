#include <iostream>
#include <map>
#include <stdexcept>
#include "ceta.hh"

using namespace ceta;
using namespace std;

/** Returns true if character is considered whitespace. */
static
bool is_whitespace(int c) {
  return (c == ' ') || (c == '\t') || (c == '\n') || (c == '\r')
      || (c == -1);
}

/** Returns true if character is parenthesis or brace. */
static
bool is_paren(int c) {
  return (c == '(') || (c == ')') || (c == '[') || (c == ']');
}
  
/**
 * This class pulls "tokens" from an input string.  Tokens are whitespace-
 * deliminted words in the stream.  Each individual parenthesis and brace is
 * considered a separate token regardless of if it has whitespace around it.
 */
class tokenizer_t {
public:
  tokenizer_t(std::istream& i)
    : i_(i) {
  }

  const string next(void) {
    string result;
    *this >> result;
    return result;
  }

  const std::vector<string> next_list(const std::string& terminal) {
    std::vector<string> result;
    std::string input;
    while ((input = next()) != terminal)
      result.push_back(input);
    return result;
  }

  tokenizer_t& operator>>(std::string& str) {
    while (is_whitespace(i_.peek()))
      i_.ignore(1);
    if (is_paren(i_.peek())) {
      str = i_.get();
    } else {
      std::vector<char> chars;
      while (!is_whitespace(i_.peek()) && !is_paren(i_.peek())) {
        chars.push_back(i_.get());
      }
      str = std::string(chars.begin(), chars.end());
    }
    return *this;
  }

  tokenizer_t& operator>>(const std::string& expected) {
    string str;
    i_ >> str;
    if (str != expected)
      throw std::runtime_error("Expected " + expected + " found " + str);
    return *this;
  }
private:
  istream& i_;
};

typedef std::pair<op_t, axiom_set_t> op_pair_t;
typedef std::map<string, op_pair_t> op_map_t;

const op_pair_t& find(const op_map_t& map, string name) {
  op_map_t::const_iterator i = map.find(name);
  if (i == map.end())
    throw std::runtime_error("Could not identify operator " + name);
  return i->second;
}

ta_t parse_ta(tokenizer_t& t) {
  bool parsing = true;
  typedef std::map<string, kind_t> kind_map_t;
  typedef std::map<string, state_t> state_map_t;
  kind_map_t kind_map;
  op_map_t op_map;
  state_map_t state_map;
  std::vector<erule_t> erules;
  std::vector<rule_t> rules;
  typedef std::vector<string>::const_iterator iter;
  while (parsing) {
    string type;
    t >> type;
    if ((type == "kind") || (type == "kinds")) {
      // Read list of kind names
      std::vector<string> names = t.next_list(".");
      // Add kinds to map.
      for (iter i = names.begin(); i != names.end(); ++i) {
        kind_t k(*i);
        kind_map.insert(make_pair(*i, k));
      }
    } else if ((type == "op") || (type == "ops")) {
      // Read operator declaration(s).
      std::vector<string> names = t.next_list(":");
      std::vector<string> inputs = t.next_list("->");
      string output = t.next();
      string delim = t.next();
      axiom_set_t axioms = none();
      if (delim == "[") {
        string next;
        while ((next = t.next()) != "]") {
          if (next == "assoc") {
            axioms |= assoc();
          } else if (next == "comm") {
            axioms |= comm();
          } else if (next == "left-id:") {
            op_t op_id = find(op_map, t.next()).first;
            axioms |= left_id(op_id);
          } else if (next == "right-id:") {
            op_t op_id = find(op_map, t.next()).first;
            axioms |= right_id(op_id);
          } else if (next == "id:") {
            op_t op_id = find(op_map, t.next()).first;
            axioms |= id(op_id);
          }
        }
      }
      // Get kinds from names.
      std::vector<kind_t> ikinds;
      ikinds.reserve(inputs.size());
      for (iter i = inputs.begin(); i != inputs.end(); ++i)
        ikinds.push_back(kind_map.find(*i)->second);
      kind_t okind = kind_map.find(output)->second;
      // Add ops to map.
      for (iter i = names.begin(); i != names.end(); ++i) {
        op_t op(*i, ikinds.begin(), ikinds.end(), okind);
        op_map.insert(make_pair(*i, make_pair(op, axioms)));
      }
    } else if (type == "state") {
      // Read state declaration(s).
      std::vector<string> names = t.next_list(":");
      string kind;
      t >> kind >> ".";
      // Get kind from name.
      kind_t k = kind_map.find(kind)->second;
      // Add states to map.
      for (iter i = names.begin(); i != names.end(); ++i) {
        state_t state(k, *i);
        state_map.insert(make_pair(*i, state));
      }
    } else if (type == "rl") {
      string name, delim;
      t >> name >> delim;
      std::vector<string> lhs;
      if (delim == "(") {
        lhs = t.next_list(")");
        t >> "->";
      }
      string rhs;
      t >> rhs >> ".";
      // If name is a state, treat as an epsilon rule
      if (state_map.find(name) != state_map.end()) {
        state_t lhs_state = state_map.find(name)->second;
        state_t rhs_state = state_map.find(rhs)->second;
        erules.push_back(erule_t(lhs_state, rhs_state));
      } else { // Otherwise this is a regular rule.
        op_t op = find(op_map, name).first;
        std::vector<state_t> lhs_states;
        lhs_states.reserve(lhs.size());
        for (iter i = lhs.begin(); i != lhs.end(); ++i)
          lhs_states.push_back(state_map.find(*i)->second);
        state_t rhs_state = state_map.find(rhs)->second;
        rule_t rule(op, lhs_states.begin(), lhs_states.end(), rhs_state);
        rules.push_back(rule);
      }
    } else if (type == "end") {
      parsing = false;
    }
  }
  theory_t theory;
  // Add kinds to theory.
  typedef kind_map_t::const_iterator kind_iter;
  for (kind_iter i = kind_map.begin(); i != kind_map.end(); ++i)
    add_kind(theory, i->second);
  // Add ops to theory.
  typedef op_map_t::const_iterator op_iter;
  for (op_iter i = op_map.begin(); i != op_map.end(); ++i) {
    add_op(theory, i->second.first);
    set_axioms(theory, i->second.first, i->second.second);
  }
  ta_t ta(theory);
  // Add states to ta.
  typedef state_map_t::const_iterator state_iter;
  for (state_iter i = state_map.begin(); i != state_map.end(); ++i)
    add_state(ta, i->second);
  // Add rules and erules to ta.
  typedef std::vector<erule_t>::const_iterator erule_iter;
  for (erule_iter i = erules.begin(); i != erules.end(); ++i)
    add_erule(ta, *i);
  typedef std::vector<rule_t>::const_iterator rule_iter;
  for (rule_iter i = rules.begin(); i != rules.end(); ++i)
    add_rule(ta, *i);
  return ta;
}

int main(int argc, char **argv) {
  tokenizer_t t(cin);
  ta_t ta = parse_ta(t);
  cerr << ta;
  test_emptiness(ta);
}
