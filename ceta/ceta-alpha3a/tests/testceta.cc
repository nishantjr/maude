#include "ceta.hh"

#include <iostream>
#include <list>
#include <set>
#include <stdexcept>

#include <boost/assign/list_of.hpp>

using namespace std;
using namespace ceta;
using namespace boost::assign;

rule_t make_rule(const op_t& op, const list<state_t>& lhs_states,
                 const state_t& rhs) {
  return rule_t(op, lhs_states.begin(), lhs_states.end(), rhs);
}

void sig_error(const std::string& str) {
  cerr << str << endl;
  *static_cast<int*>(NULL) = 2;
}

void test_simple() {
  theory_t theory;
  kind_t k("k"); add_kind(theory, k);
  kind_t l("l"); add_kind(theory, l);
  op_t a = make_constant("a", k); add_op(theory, a);
  op_t b = make_constant("b", l); add_op(theory, b);
  op_t c = make_constant("c", k); add_op(theory, c);
  op_t f = make_binary_op("f", k, k, k); add_op(theory, f);
  set_axioms(theory, f, assoc());
  op_t g = make_binary_op("g", k, k, k); add_op(theory, g);
  set_axioms(theory, g, comm());
  op_t h = make_binary_op("h", k, k, k); add_op(theory, h);
  set_axioms(theory, h, assoc() | comm());

  ta_t ta(theory);
  state_t k1(k, "k1"); add_state(ta, k1);
  state_t k2(k, "k2"); add_state(ta, k2);

  add_rule(ta, make_constant_rule(a, k1));
  add_rule(ta, make_binary_rule(f, k1, k1, k2));

  test_result_t result = test_emptiness(ta);
  if (!result) {
    cerr << "ERR " << counterexample(result) << endl;
    sig_error("Automata expected to be empty");
  }

  set_predicate(ta, k2);
  result = test_emptiness(ta);
  if (result)
    sig_error("Automata expected to be nonempty");
}

void test_and(void) {
  theory_t theory;
  // Add kind.
  kind_t k("Bool"); add_kind(theory, k);

  // Add op declarations
  op_t true_op  = make_constant("true", k);  add_op(theory, true_op);
  op_t false_op = make_constant("false", k); add_op(theory, false_op);
  op_t and_op = make_binary_op("and", k, k, k); add_op(theory, and_op);
  set_axioms(theory, and_op, assoc() | comm());

  ta_t ta(theory);

  // Add state declarations
  state_t term1(k, "Term1"); add_state(ta, term1);
  state_t term2(k, "Term2"); add_state(ta, term2);
  state_t cbool(k, "cBool"); add_state(ta, cbool);
  state_t rbool(k, "rBool"); add_state(ta, rbool);

  add_rule(ta, make_constant_rule(true_op, cbool));
  add_rule(ta, make_constant_rule(true_op, term1));
  add_rule(ta, make_constant_rule(false_op, cbool));
  add_rule(ta, make_constant_rule(false_op, term2));
  add_rule(ta, make_rule(and_op, list_of(term1)(cbool), rbool));
  add_rule(ta, make_rule(and_op, list_of(term2)(cbool), rbool));

  set_predicate(ta, !cbool & !rbool);

  test_result_t result = test_emptiness(ta);
}

void test_nat_mset_sum_id() {
  theory_t theory;

  kind_t k("k"); add_kind(theory, k);

  op_t zero = make_constant("0", k);        add_op(theory, zero);
  op_t succ = make_unary_op("s", k, k);     add_op(theory, succ);
  op_t plus = make_binary_op("+", k, k, k); add_op(theory, plus);
  set_axioms(theory, plus, comm() | id(zero));
  op_t times = make_binary_op("*", k, k, k); add_op(theory, times);
  op_t cat = make_binary_op("__", k, k, k); add_op(theory, cat);
  set_axioms(theory, cat, assoc() | comm());
  op_t sum = make_unary_op("sum", k, k);    add_op(theory, sum);

  ta_t ta(theory);

  // Add states for sorts
  state_t  cNat(k, "cNat");  add_state(ta, cNat);
  state_t cMSet(k, "cMSet"); add_state(ta, cMSet);
  state_t  dNat(k, "dNat");  add_state(ta, dNat);
  state_t dMSet(k, "dMSet"); add_state(ta, dMSet);
  state_t  rNAT(k, "rNAT");  add_state(ta, rNAT);
  state_t  kNAT(k, "kNAT");  add_state(ta, kNAT);

  // Add states for specific terms in equations
  state_t    q0(k, "q0");    add_state(ta, q0); // Accepts 0
  state_t    q1(k, "q1");    add_state(ta, q1); // Accepts 0 cMSet
  state_t    q2(k, "q2");    add_state(ta, q2); // Accepts s(cNat)
  state_t    q3(k, "q3");    add_state(ta, q3); // Accepts s(cNat) cMSet

  // Epsilon transitions for subsort declarations
  add_erule(ta, erule_t(cNat, cMSet));
  add_erule(ta, erule_t(dNat, dMSet));

  // Zero
  // 0 => cNAT
  add_rule(ta, make_constant_rule(zero, cNat));
  // 0 => q0
  add_rule(ta, make_constant_rule(zero, q0));
  // kNAT
  add_rule(ta, make_constant_rule(zero, kNAT));

  // Succ
  // s(cNAT) => cNAT
  add_rule(ta, make_rule(succ, list_of(cNat), cNat));
  //   s(cNat) => q2
  add_rule(ta, make_rule(succ, list_of(cNat), q2));
  // kNAT
  add_rule(ta, make_rule(succ, list_of(kNAT), kNAT));
  // rNAT
  add_rule(ta, make_rule(succ, list_of(rNAT), rNAT));

  // Plus
  // cNat + cNat => dNat
  add_rule(ta, make_rule(plus, list_of(cNat)(cNat), dNat));
  // +(s(cNat), cNat) => rNAT
  add_rule(ta, make_rule(plus, list_of(q2)(cNat), rNAT));
  // Rule for kNAT
  add_rule(ta, make_rule(plus, list_of(kNAT)(kNAT), kNAT));
  // Rules for closing rNAT
  add_rule(ta, make_rule(plus, list_of(rNAT)(kNAT), rNAT));
  add_rule(ta, make_rule(plus, list_of(kNAT)(rNAT), rNAT));

  // Times
  // cNat * cNat => dNat
  add_rule(ta, make_rule(times, list_of(cNat)(cNat), dNat));
  // 0 * cNat => rNAT
  add_rule(ta, make_rule(times, list_of(q0)(cNat), rNAT));
  // s(cNat) * cNat => rNAT
  add_rule(ta, make_rule(times, list_of(q2)(cNat), rNAT));
  // Rules for kNAT
  add_rule(ta, make_rule(times, list_of(kNAT)(kNAT), kNAT));
  // Rules for closing rNAT
  add_rule(ta, make_rule(times, list_of(rNAT)(kNAT), rNAT));
  add_rule(ta, make_rule(times, list_of(kNAT)(rNAT), rNAT));

  // Cat
  // cMSet cMSet => cMSet
  add_rule(ta, make_rule(cat, list_of(cMSet)(cMSet), cMSet));
  // 0 cMSet => q1
  add_rule(ta, make_rule(cat, list_of(q0)(cMSet), q1));
  // s(cNat) cMSet => q3
  add_rule(ta, make_rule(cat, list_of(q2)(cMSet), q3));
  // kNAT
  add_rule(ta, make_rule(cat,  list_of(kNAT)(kNAT), kNAT));
  // rNAT
  add_rule(ta, make_rule(cat, list_of(rNAT)(kNAT), rNAT));
  add_rule(ta, make_rule(cat, list_of(kNAT)(rNAT), rNAT));

  // Sum
  // sum(cMSet) => dNat
  add_rule(ta, make_rule(sum, list_of(cMSet), dNat));
  // sum(0) => rNAT
  add_rule(ta, make_rule(sum, list_of(q0), rNAT));
  // sum(s(Nat)) => rNAT
  add_rule(ta, make_rule(sum, list_of(q2), rNAT));
  // sum(0 NatMSet) =>rNAT
  add_rule(ta, make_rule(sum, list_of(q1), rNAT));
  // sum(s(Nat) NatMSet) => rNAT
  add_rule(ta, make_rule(sum, list_of(q3), rNAT));
  // kNAT
  add_rule(ta, make_rule(sum,  list_of(kNAT), kNAT));
  // rNAT
  add_rule(ta, make_rule(sum, list_of(rNAT), rNAT));

  set_predicate(ta, !rNAT & (dNat & !cNat | dMSet & !cMSet));

  test_result_t result = test_emptiness(ta);

  if (!result) {
    cerr << "ERR "
         << counterexample(result)
         << " "
         << reachable_set(result)
         << endl;
    sig_error("Automata expected to be empty");
  }
}

void test_intersect() {
  theory_t theory;
  kind_t k = *add_kind(theory, kind_t("k"));
  op_t a = *add_op(theory, make_constant("a", k));

  ta_t ta(theory);
  state_t p = *add_state(ta, state_t(k, "p"));
  set_predicate(ta, p);

  add_rule(ta, make_constant_rule(a, p));

  ta_t t2 = ta;
  ta_t t3 = ta & t2; // infinite loop
  cerr << t3 << endl; 
}


int main(int argc, char **argv) {
  try {
    // Test number with natural numbers and multisets
    test_simple();
    test_and();
    test_nat_mset_sum_id();
    test_intersect();
    return 0;
  } catch (const exception& e) {
    cerr << e.what() << endl;
    return 1;
  }
}
