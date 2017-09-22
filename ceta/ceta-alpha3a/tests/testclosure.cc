#include "closure.hh"

#include <iostream>

using namespace std;
using namespace ceta;
using namespace ceta::closure;

void test_closure() {
  const epsilon_closure_t<string, size_t> closure;
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
