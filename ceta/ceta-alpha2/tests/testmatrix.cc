#include <iostream>
#include <stdexcept>
#include <vector>


#include "boost/rational.hpp"
#include "matrix.hh"
#include "writer.hh"

using namespace ceta;
using namespace std;

typedef boost::rational<long long> rational;
using boost::gcd;

void error(const string& msg) {
  *(static_cast<int*>(NULL)) = 1;
  throw logic_error(msg);
}


// Test GCD
void testGCD() {
  if (gcd( 2,  3) != 1) error("GCD1");
  if (gcd( 4, -6) != 2) error("GCD2");
  if (gcd(-9, -9) != 9) error("GCD3");
  if (gcd( 0,  0) != 0) error("GCD4");
  if (gcd( 0, -4) != 4) error("GCD5");
  if (gcd(-4,  0) != 4) error("GCD6");
}

// Test rational
void testRat() {
  rational a(1, 2);
  rational b(2, 3);
  rational c(1, 3);
  rational d(3, 4);
  if (a + b <= rational(1)) error("7/6 <= 1");
  if (a - b > rational(0)) error("-1/6 > 0");
  if (a + b == d) error("7/6 == 3/4");
  if (a * b != c) {
    cout << a << " * " << b << " = " << a * b << " != " << c << endl;
    error("1/3 != 1/3");
  }
  if (a / b < d) error("");
  if (a + d > rational(5, 4)) error("");

  a = b; 
  a += c;
  if (a != rational(1)) error("1 != 1"); 
  a -= c;
  if (a != b) error("2/3 != 2/3");

  a *= d;
  if (a != rational(1, 2)) error("1/2 != 1/2");
  a /= c;
  if (a != rational(3, 2)) error("3/2 != 3/2");


//  if (gcd(rational(9, 10), rational(6, 25)) != rational(3, 50))
//    error("gcdrat");
}

void testArray() {
  // axpy
  int x[] = {0, 1, 2, 3};
  int y[] = {6, 5, 4, 3};

  axpy(2, x, x + 3, y);
  if (y[1] != 7) error("A1");
  if (y[3] != 3) error("A2");
  scal(2, y + 1, y + 4);
  if (y[0] != 6) error("A3");
  if (y[2] != 16) error("A4");


  rational u[] = {rational(1, 2), rational(3, 2)};
  rational v[] = {rational(3, 4), rational(2, 1)};
  axpy(rational(2, 1), u + 1, u + 2, v);
  if (v[0] != rational(15, 4)) error("A5");
}

void testLU() {
  int avals[] =
      { 1,  2,  3,
        2,  5,  6,
        3,  1,  9,
        4,  3, 12};

  LU<rational> a(4, 3, row_matrix_view<int>(4, 3, avals));
  if (a.nr() != 4) error("a.nr");
  if (a.nc() != 3) error("a.nc");
  if (a.rank() != 2) {
    cerr << "rank " << a.rank() << endl;
    error("a.rank");
  }
  const rational* afn(a.zero_fn(0));
  if (afn[0] + rational(3) * afn[2] != rational(0)) error("azero1");
  if (afn[1] != rational(0)) error("azero2");

  int b[] = {4, 9, 7, 11};
  rational x[3];
  if (a.solve(b, x) == false) error("solve");
  if (x[0] != rational(2)) error("x[0]");
  if (x[1] != rational(1)) error("x[1]");

  
  int m2vals[] =
      {1, 2, 4,
       2, 5, 6,
       3, 1, 9};
  LU<rational> m2(3, 3, row_matrix_view<int>(3, 3, m2vals));


  if (a.det() != 0) error("a.det()");
  if (m2.det() != -13) error("m2.det()");

  int m3vals[] = 
      {4, 10, 1,  0, -2,
       4, 10, 1, -2,  0,
       7, 13, 4,  0  -2};
  LU<rational> m3(3, 5, row_matrix_view<int>(3, 5, m3vals));
  if (m3.rank() != 3) error("m3.rank");

  int m4vals[] = 
      { 0,  0, -1,
        0, -2,  0,
        1, -1,  0};
  LU<rational> m4(3, 3, row_matrix_view<int>(3, 3, m4vals));
  int b4[] = {-1, -2, 0};
  int ex4[] = {1, 1, 1};
  if (m4.solve(b4, x) == false) error("m4.solve(b4.x) failed");
  if (vector<rational>(x, x + 3) != vector<rational>(ex4, ex4 + 3)) {
    cerr << "bad m4 " << make_range_writer(x, x + 3) << endl;
    error("m4.solve(b4, x) incorrect");
  }

  // Test cases where number of equations or variables equals 0.
  LU<rational> m20(2, 0, row_matrix_view<int>(0, 0, m3vals));
  LU<rational> m03(0, 3, row_matrix_view<int>(0, 0, m3vals));
  LU<rational> m00(0, 0, row_matrix_view<int>(0, 0, m3vals));
  if (m20.rank() != 0) error("m20.rank");
  if (m03.rank() != 0) error("m03.rank");
  if (m00.rank() != 0) error("m00.rank");
  int c[2] = {0, 0};
  int d[2] = {0, 1};
  if (m20.solve(c, x) == false) error("m20.solve(c, x)");
  if (m20.solve(d, x) == true)  error("m20.solve(d, x)");
  if (m03.solve(c, x) == false) error("m03.solve(c, x)");
  if (m00.solve(c, x) == false) error("m03.solve(c, x)");
  if (m00.solve(d, x) == false) error("m00.solve(d, x)");
}

int main(int argc, char **argv)
{
  try {
    testGCD();
    testRat();
    testArray();
    testLU();

    return 0;
  } catch (const exception& e) {
    cerr << e.what() << endl;
    return 1;
  }
}
