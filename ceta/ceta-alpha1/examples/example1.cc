#include <iostream>
#include <ceta/ceta.hh>

using namespace ceta;
using namespace std;

int main(int argc, char **argv) {
  // Construct theory with constants a and b and AC symbol f.
  theory_t theory;
  kind_t k = *add_kind(theory, kind_t("k"));
  op_t a = *add_op(theory, make_constant("a", k));
  op_t b = *add_op(theory, make_constant("b", k));
  op_t f = *add_op(theory, make_binary_op("f", k, k, k));
  set_axioms(theory, f, assoc() | comm());

  // Construct automata with given theory with states qa and qb.
  ta_t ta_base(theory);
  state_t qa = *add_state(ta_base, state_t(k, "qa"));
  state_t qb = *add_state(ta_base, state_t(k, "qb"));
  // Add rules so that in ta_base, q -> qa and b -> qe.
  add_rule(ta_base, make_constant_rule(a, qa));
  add_rule(ta_base, make_constant_rule(b, qb));

  // Construct tree automaton that recognizes flattened terms where number of
  // occurences of a and b are equal.
  ta_t ta_eq = ta_base;
  // Declare and add state qe.
  state_t qe = *add_state(ta_eq, state_t(k, "qe"));
  set_predicate(ta_eq, qe);
  // Add rule: f(qa, qb) -> qe and f(qe, qe) -> qe
  add_rule(ta_eq, make_binary_rule(f, qa, qb, qe));
  add_rule(ta_eq, make_binary_rule(f, qe, qe, qe));

  // Construct tree automaton by extending ta_eq that recognizes flattened
  // terms where number of occurences of a are greater than number of
  // occurences of b.
  ta_t ta_gt = ta_eq;
  state_t qge = *add_state(ta_gt, state_t(k, "qge"));
  set_predicate(ta_gt, qge & !qe);
  // Add rules so qge accepts terms where number of occurences of a >= number
  // of occurences of b.
  add_erule(ta_gt, erule_t(qe, qge));
  add_rule(ta_gt, make_binary_rule(f, qa, qge, qge));

  // Verify that ta_eq & ta_gt is empty.
  test_result_t result = test_emptiness(ta_eq & ta_gt);
  if (!result)
    cerr << "ta_eq & ta_gt expected to be empty." << endl;
  // Verify that !ta_eq & ta_gt is not empty.
  result = test_emptiness(!ta_eq & ta_gt);
  if (result) {
    cerr << "!ta_eq & ta_gt expected to be not empty." << endl;
  } else {
    //Print counterexample and satisifying state set.
    cerr << "counterexample: " << counterexample(result)
         << " set: " << reachable_set(result)
         << endl; 
  }

}
