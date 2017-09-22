#include <iostream>
#include <ceta/ceta.hh>

using namespace ceta;
using namespace std;

/************
[signature]
ac: f
const: a
[T-rule(p): T]
a -> r
q -> p
e(q,q) -> q
f(r,r) -> q
f(q,q) -> q
f(p,p) -> p
*************/


class state_set_receiver_t {
  public:
  bool operator()(const std::set<state_t>& states){
    return false;
  }
};

const void populate_reachable_states(const ta_t& ta,
                   state_set_receiver_t& r) {
  subset_constructor_t sc(ta);
  while (sc.has_next() || !sc.is_complete()) {
    // This is just so that the same loop
    if (sc.has_next()) {
      const std::set<state_t>& set = sc.next_set();
      if (r(set))
        return;
      sc.pop_next();
    } else {
      sc.work();
    }
  }
}

const void populate_reachable_states(const ta_t& ta) {
  state_set_receiver_t nop;
  populate_reachable_states(ta, nop);
}

void test(void) {
  theory_t theory;
  kind_t k = *add_kind(theory, kind_t("k"));
  op_t a = *add_op(theory, make_constant("a", k));
  op_t f = *add_op(theory, make_binary_op("f", k, k, k));
  op_t e = *add_op(theory, make_binary_op("e", k, k, k));
  set_axioms(theory, f, assoc() | comm());

  ta_t ta(theory);
  state_t p = *add_state(ta, state_t(k, "p"));
  state_t q = *add_state(ta, state_t(k, "q"));
  state_t r = *add_state(ta, state_t(k, "r"));

  set_predicate(ta, state_predicate_t(k, false));

  add_rule(ta, make_constant_rule(a, r));
  add_erule(ta, erule_t(q, p));
  add_rule(ta, make_binary_rule(e, q, q, q));
  add_rule(ta, make_binary_rule(f, r, r, q));
  add_rule(ta, make_binary_rule(f, q, q, q));
  add_rule(ta, make_binary_rule(f, p, p, p));

  populate_reachable_states(ta);
}

int main(int argc, char **argv) {
  for (size_t i = 0; i != 10000; ++i)
    test();
  return 0;
}
