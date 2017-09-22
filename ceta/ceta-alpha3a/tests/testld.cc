#include <iostream>
#include <sstream>
#include <set>
#include <stdexcept>
#include <vector>

#include "ldsolver.hh"
#include "writer.hh"

using namespace ceta;
using namespace std;

void error(const string& msg) {
  cerr << msg << endl;
  *static_cast<int*>(NULL) = 1;
  throw logic_error(msg);
}

void check_solver(const string& id,
                  ld_solver_t& solver,
                  size_t expected_count,
                  unsigned* expected) {

  size_t nc(solver.nc());
  set<vector<unsigned> > expected_set;
  for (size_t i(0); i != expected_count; ++i) {
    expected_set.insert(vector<unsigned>(
          expected + i * nc, expected + (i + 1) * nc));
  }
  
  size_t total_found(0);
  vector<unsigned> sol(nc);
  while (solver.next(sol)) {
    if (expected_set.find(sol) != expected_set.end()) {
      ++total_found;
    } else {
      cerr << "unexpected [" << make_range_writer(sol.begin(), sol.end())
           << "]" << endl;
      error("Found unexpected solution.");
    }
  }
  if (total_found != expected_count) {
    ostringstream o;
    o << id << ": Found " << total_found << " solutions,"
      << " and expected " << expected_count << "." << endl;
    error(o.str());
  }
}

void testld(void) {
  int a1[] = {
     3,  3,  3,
     4,  4,  7,
    10, 10, 13,
     1,  1,  4,
     0, -2,  0,
    -2,  0, -2
  };
  ld_solver_t s1(3, 6, a1);
  unsigned e1[] = {2, 0, 0, 0, 3, 3};
  check_solver("s1", s1, 1, e1);

//  ld_solver_t s02(0, 2, NULL);
//  // Expected solutions for s02
//  set<vector<unsigned> > e0;
//  unsigned e02[] =
//    {1, 0,
//     0, 1};
//  check_solver("s02", s02, 2, e02);
//  
//  ld_solver_t s20(3, 0, NULL);
//  check_solver("s20", s20, 0, NULL);
//
//  ld_solver_t s00(0, 0, NULL);
//  check_solver("s00", s00, 0, NULL);
//
  int a2[] = {
     0,  0,  1,
     1,  1,  0,
     0, -2, -1,
    -1,  0,  0
  };

  ld_solver_t s2(3, 4, a2);
  unsigned e2h[] = {1, 2, 1, 2};
  check_solver("s2-1", s2, 1, e2h);
  int v2[] = {1, 0, -1};
  s2.solve(v2);
  unsigned e2n[] = {0, 2, 1, 1};
  check_solver("s2-2", s2, 1, e2n);
}

int main(int argc, char **argv) {
  try {
    testld();
    return 0;
  } catch (const exception& e) {
    cerr << e.what() << endl;
    return 1;
  }
}
