#include "membership.hh"
#include <iostream>

using namespace ceta;

void sig_error(const std::string& str) {
  std::cerr << str << std::endl;
  *static_cast<int*>(NULL) = 2;
}

void test_membership() {
  theory_t th;
  kind_t k = *add_kind(th, kind_t("k"));
  op_t a = *add_op(th, make_constant("a", k));
  op_t b = *add_op(th, make_constant("b", k));
  op_t e = *add_op(th, make_unary_op("e", k, k));
  op_t f = *add_op(th, make_binary_op("f", k, k, k));
  set_axioms(th, f, assoc());
  op_t g = *add_op(th, make_binary_op("g", k, k, k));
  set_axioms(th, g, comm());
  op_t h = *add_op(th, make_binary_op("h", k, k, k));
  set_axioms(th, h, assoc() | comm());

  ta_t ta(th);
  state_t sa = *add_state(ta, state_t(k, "sa"));
  add_rule(ta, make_constant_rule(a, sa));
  state_t sb = *add_state(ta, state_t(k, "sb"));
  add_rule(ta, make_constant_rule(b, sb));
  state_t se = *add_state(ta, state_t(k, "sa"));
  add_rule(ta, make_unary_rule(e, sa, se));

  state_t sg = *add_state(ta, state_t(k, "sg"));
  add_rule(ta, make_binary_rule(g, sb, se, sg));

  term_t t_a = make_constant(th, a);
  term_t tb = make_constant(th, b);

  std::vector<term_t> terms;
  terms.push_back(t_a);
  term_t te(th, e, terms.begin(), terms.end());

  terms[0] = te;
  terms.push_back(tb);
  // Makes g(e(a), b)
  term_t tg(th, g, terms.begin(), terms.end());

  std::set<state_t> reachables = reachable_states(ta, tg);

  std::set<state_t> expected_result;
  expected_result.insert(sg);
  if (reachables != expected_result)
    sig_error("Unexpected result");
}

int main(int argc, char **argv) {
  try {
    test_membership();
    return 0;
  } catch (const std::exception& e) {
    std::cerr << e.what() << std::endl;
    return 1;
  }
}
