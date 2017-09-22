#include "closure.hh"

#include <iostream>

using namespace std;
using namespace ceta;

void test_closure() {
  theory_t theory;
  ta_t ta(theory);
  closure_t closure(ta);
  //TODO: Actually test closure
}

int main(int argc, char **argv) {
  try {
    test_closure();
    return 0;
  } catch (const exception& e) {
    cerr << e.what() << endl;
    return 1;
  }
}
