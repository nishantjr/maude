#include<iostream>
#include<stdexcept>

#include "matrix.hh"
#include "sls.hh"
#include "writer.hh"

using namespace std;
using namespace ceta;

void error(const string& msg) {
  *static_cast<int*>(NULL) = 1;
  throw logic_error(msg);
}

template<typename T>
linear_set_group init(size_t dim,
                      size_t constant_count, const T constants,
                      size_t period_count, const T periods) {
  linear_set_group result(dim);

  for (size_t i(0); i != constant_count; ++i)
    result.insert_constant(constants[i]);

  for (size_t i(0); i != period_count; ++i)
    result.insert_period(periods[i]);
  return result;
}

void testSLS(void) {
  unsigned c1[][3] 
    = {{0, 0, 0},
       {1, 1, 1}};
  unsigned p1[][3] 
    = {{1, 1, 1},
       {4, 4, 7},
       {10, 10, 13},
       {1, 1, 4}};
  linear_set_group g1(init(3, 2, c1, 4, p1));

  semilinear_set s1(3); s1.insert(g1);

  unsigned v1[] = {15, 15, 10};
  unsigned v2[] = {11, 11, 14};
  semilinear_set a(3);

  unsigned c2[][3] = {{2, 0, 2}};
  unsigned p2[][3] = {{0, 2, 0}, {2, 0, 2}};
  linear_set_group g2(init(3, 1, c2, 2, p2));

  semilinear_set s2(3); s2.insert(g2);

  semilinear_set s3(intersect(s1, s2));

  semilinear_set s4(independent_periods(s1));

  cerr << "min_size " << min_size_set(3, 2) << endl;

  if (complement(complete_set(3)).dim() != 3) error("complement3dim");
  if (!is_empty(complement(complete_set(3)))) error("complement3empty");

  semilinear_set s5(complement(s1));

  if (s5.dim() != 3) error("s5.dim");

  if (!member(v1, s5)) error("!s5->member(v1)");
  if ( member(v2, s5)) error(" s5->member(v2)");

  semilinear_set s5_copy;

  s5_copy = s5;
  if (s5_copy.dim() != 3) error("s5_copy.dim");

  unsigned c6[][8]
    = {{0, 0, 1}, {1, 1, 0}};
  unsigned c7[][8]
    = {{1, 0, 0}, {0, 2, 1}};

  linear_set_group g6(init(3, 2, c6, 2, c6));
  semilinear_set s6(3); s6.insert(g6);
  linear_set_group g7(init(3, 2, c7, 2, c7));
  semilinear_set s7(3); s7.insert(g7);


  cerr << "intersect s6 s7" << endl;
  semilinear_set s8(intersect(s6, s7));
  cerr << "s6 /\\ s7 " << s8 << endl;
}

//000 + 111 114
//001 + 001 111
//
// x =/= y
// 010 + 010 001 110
// 100 + 100 001 110

// z > 4x
//001 + 001 114

// x > z
//110 + 110 111

// (z - x % 3) != 0
//001 002 + 111 114


// x = y > z
//110 + 110 111

//001 + 001 

int main(int argc, char **argv)
{
  try {
    testSLS();

    return 0;
  } catch (const exception& e) {
    cerr << e.what() << endl;
    return 1;
  }
}
