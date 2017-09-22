#include "closure.hh"

#include <iostream>

using namespace std;
using namespace ceta;
using namespace ceta::closure;

void test_closure(const epsilon_closure_t& closure) {
  kind_t k("k");
  state_t cNat(k, "cNat");
  state_t dNat(k, "dNat");
  state_t cMSet(k, "cMSet");
}

int main(int argc, char **argv) {
  try {
    return 0;
  } catch (const exception& e) {
    cerr << e.what() << endl;
    return 1;
  }
}
