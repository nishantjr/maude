#include "ceta.hh"

#include <iostream>
#include <list>
#include <set>
#include <stdexcept>

#include <boost/assign/list_of.hpp>

using namespace std;
using namespace ceta;
using namespace boost::assign;

op_t make_op(const std::string& name,
             const list<kind_t>& inputs,
             kind_t output) {
  return op_t(name, inputs.begin(), inputs.end(), output);
}

rule_t make_rule(const op_t& op, const list<state_t>& lhs_states,
                 const state_t& rhs) {
  return rule_t(op, lhs_states.begin(), lhs_states.end(), rhs);
}

//void add_transition(tree_automaton_t& a, op_t o, const list<state_t>& args, state_t rhs) {
//  state_t arg_elts[args.size()];
//  std::copy(args.begin(), args.end(), arg_elts);
//  a.add_transition(o, arg_elts, arg_elts + args.size(), rhs);
//}

void sig_error(const std::string& str) {
  cerr << str << endl;
  *static_cast<int*>(NULL) = 2;
}

void check_model(const state_predicate_t& p,
                 const set<state_t>& set,
                 bool expected,
                 const std::string& pred_name,
                 const std::string& set_name) {
  std::string pos = (expected ? "" : "not ");
  std::string neg = (expected ? "not " : "");
//  if (p.is_model(set) != expected)
//    sig_error(set_name + " is " + neg + "a model of " + pred_name);
//  if ((!p).is_model(set) == expected)
//    sig_error(set_name + " is " + pos + "a model of !" + pred_name);
}

void test_predicate() {
//  kind_t k("k");
//
//  theory_t theory;
//  theory.add_kind(k);
//
//  ta_t ta(theory);
//
//  state_t a(k, "a"); ta.add_state(a);
//  state_t b(k, "b"); ta.add_state(b);
//  state_t c(k, "c"); ta.add_state(c);
//  state_t d(k, "d"); ta.add_state(d);
//
//  state_predicate_t ap(a);
//  state_predicate_t bp(b);
//
//  set<state_t> emptyset;
//
//  set<state_t> aset;
//  aset.insert(a);
//  
//  set<state_t> abset;
//  abset.insert(a);
//  abset.insert(b);
//
//  check_model(ap, emptyset, false, "a", "emptyset");
//
//  cerr << !(a & b) << endl;
//  cerr << !(a | b) << endl;
//
//  check_model(a & b, abset, true, "a & b", "abset");
//  check_model(a & b & c, abset, false, "a & b & c", "abset");
//  check_model(a | b, abset, true, "a | b", "abset");
//  check_model(a | b, aset, true, "a | b", "aset");
//  check_model(a | b, emptyset, false, "a | b", "emptyset");
//  check_model(state_predicate_t(true), aset, true, "true", "aset");
//  check_model(state_predicate_t(false), aset, false, "false", "aset");
//
}

void test_simple() {
  theory_t theory;
  kind_t k("k"); add_kind(theory, k);
  kind_t l("l"); add_kind(theory, l);
  op_t a = make_constant("a", k); add_op(theory, a);
  op_t b = make_constant("b", l); add_op(theory, b);
  op_t c = make_constant("c", k); add_op(theory, c);
  op_t f = make_binary_op("f", k, k, k); add_op(theory, f);
  set_axioms(theory, a, assoc() | comm());
  op_t g = make_binary_op("g", k, k, k); add_op(theory, g);
  set_axioms(theory, g, comm());

  ta_t ta(theory);
  state_t k1(k, "k1"); add_state(ta, k1);

//  add_transition(ta, a, no_args(), k1);
//
//  emptiness_result result = ta.check_emptiness();
//  if (! result.is_empty()) {
//    cerr << "ERR " << result.accepted_term() << endl;
//    sig_error("Automata expected to be empty");
//  }
}

void test_nat_mset_sum() {
//  tree_automaton_t ta;
//  kind_t k = ta.add_kind("k");
//
//  // Add operator declarations
//  op_t zero = add_op(ta, "0", constant(), k);
//  op_t succ = add_op(ta, "s", list_of(k), k);
//  op_t plus = add_op(ta, "+", list_of(k)(k), k);
//  ta.add_comm_axiom(plus);
//  op_t cat  = add_op(ta, "__", list_of(k)(k), k);
//  ta.add_assoc_axiom(cat);
//  ta.add_comm_axiom(cat);
//  op_t sum  = add_op(ta, "sum", list_of(k), k);
//
//  // Add states for sorts
//  state_t  cNat = ta.add_state(k, "cNat");
//  state_t cMSet = ta.add_state(k, "cMSet");
//  state_t  dNat = ta.add_state(k, "dNat");
//  state_t dMSet = ta.add_state(k, "dMSet");
//  state_t  rNAT = ta.add_state(k, "rNAT");
//  state_t  kNAT = ta.add_state(k, "kNAT");
//
//  // Add states for specific terms in equations
//  state_t q0 = ta.add_state(k, "q0"); // Accepts 0
//  state_t q1 = ta.add_state(k, "q1"); // Accepts 0 cMSet 
//  state_t q2 = ta.add_state(k, "q2"); // Accepts s(cNat)
//  state_t q3 = ta.add_state(k, "q3"); // Accepts s(cNat) cMSet
//
//  // Add Epsilon transitions for subsort declarations
//  ta.add_transition(cNat, cMSet);
//  ta.add_transition(dNat, dMSet);
//
//  // Rules for constructor subsignature
//  add_transition(ta, zero, no_args(), cNat);
//  add_transition(ta, succ, list_of(cNat), cNat);
//  add_transition(ta, cat, list_of(cMSet)(cMSet), cMSet);
//
//  // Rules for defined signature
//  add_transition(ta, plus, list_of(cNat)(cNat), dNat);
//  add_transition(ta, sum, list_of(cMSet), dNat);
//
//  // Rules for recognizing terms used in equations:
//  //   0 => q0
//  add_transition(ta, zero, no_args(), q0);
//  //   s(cNat) => q2
//  add_transition(ta, succ, list_of(cNat), q2);
//  //   +(s(cNat), cNat) => rNAT
//  add_transition(ta, plus, list_of(q2)(cNat), rNAT);
//  //   +(0, 0) => rNAT
//  add_transition(ta, plus, list_of(q0)(q0), rNAT);
//  
//  // Recognize sum(0 NatMSet) =>rNAT
//  add_transition(ta, cat, list_of(q0)(cMSet), q1);
//  add_transition(ta, sum, list_of(q1), rNAT);
//  // Recognize sum(s(Nat) NatMSet) => rNAT
//  add_transition(ta, cat, list_of(q2)(cMSet), q3);
//  add_transition(ta, sum, list_of(q3), rNAT);
//  // Recognize sum(0) => rNAT
//  add_transition(ta, sum, list_of(q0), rNAT);
//  // Recognize sum(s(Nat)) => rNAT
//  add_transition(ta, sum, list_of(q2), rNAT);
//
//  // Rules for maintaining rNat
//  add_transition(ta, succ, list_of(rNAT), rNAT);
//  add_transition(ta, cat, list_of(rNAT)(kNAT), rNAT);
//  add_transition(ta, cat, list_of(kNAT)(rNAT), rNAT);
//  add_transition(ta, sum, list_of(rNAT), rNAT);
//
//  // Rules for kNat
//  add_transition(ta, zero, no_args(), kNAT);
//  add_transition(ta, succ, list_of(kNAT), kNAT);
//  add_transition(ta, cat, list_of(kNAT)(kNAT), kNAT);
//  add_transition(ta, plus, list_of(kNAT)(kNAT), kNAT);
//  add_transition(ta, sum, list_of(kNAT), kNAT);
//  
//  ta.predicate(k) = !rNAT & (dNat & !cNat | dMSet & !cMSet);
//
//  emptiness_result result = ta.check_emptiness();
//  if (! result.is_empty()) {
//    //const set<state>& states(result->second);
//    //for (set<state>::const_iterator i(states.begin());
//    //     i != states.end();
//    //     ++i) {
//    //  cerr << *i << " ";
//    //}
//    //cerr << endl;
//    sig_error("Automata expected to be empty");
//  }
}

template<typename T>
ostream& operator<<(ostream& o, const set<T>& s) {
  o << "{";
  typedef typename set<T>::const_iterator set_iter;
  set_iter i = s.begin();
  set_iter end = s.end();
  if (i != end) {
    o << *i;
    ++i;
    while (i != end) {
      o << ", " << *i;
      ++i;
    }
  }
  o << "}";
  return o;
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
  add_rule(ta, make_rule(zero, list<state_t>(), kNAT)); 

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

int main(int argc, char **argv) {
  try {
    test_predicate();
    // Test number with natural numbers and multisets
//   test_simple();
//    test_nat_mset_sum();
    test_nat_mset_sum_id();
    return 0;
  } catch (const exception& e) {
    cerr << e.what() << endl;
    return 1;
  }
}
