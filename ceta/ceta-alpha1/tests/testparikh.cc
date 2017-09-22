#include <algorithm>
#include <iostream>
#include <stdexcept>
#include <list>
#include <vector>

#include <boost/assign/list_of.hpp>
#include "parikh.hh"
#include "sls.hh"
#include "writer.hh"

using namespace std;
using boost::assign::list_of;
using namespace ceta;
using namespace ceta::cfg;

void error(const string& msg) {
  *(static_cast<int*>(NULL)) = 1;
  throw logic_error(msg);
}

void add(cfg_t& g, const list<symbol_t>& lhs, symbol_t rhs) {
  symbol_t lhs_elts[lhs.size()];
  std::copy(lhs.begin(), lhs.end(), lhs_elts);
  g.add_transition(lhs_elts, lhs_elts + lhs.size(), rhs);
}

void add1(cfg_t& g, symbol_t lhs, symbol_t rhs) {
  g.add_transition(lhs, rhs);
}

void test_simple() {
  cfg_t g;

  symbol_t t0 = g.add_terminal("0"); // {cNat, cMSet, kNAT, q0}
  symbol_t t1 = g.add_terminal("1"); // {cNat, cMSet, kNAT, q2}
  symbol_t t2 = g.add_terminal("2"); // {dNat, dMSet, kNAT, rNAT}

  symbol_t cNat  = g.add_nonterminal( "cNat");
  symbol_t cMSet = g.add_nonterminal("cMSet");
  symbol_t dNat  = g.add_nonterminal( "dNat");
  symbol_t dMSet = g.add_nonterminal("dMSet");
  symbol_t rNAT  = g.add_nonterminal( "rNAT");
  symbol_t kNAT  = g.add_nonterminal( "kNAT");
  symbol_t q0    = g.add_nonterminal(   "q0");
  symbol_t q1    = g.add_nonterminal(   "q1");
  symbol_t q2    = g.add_nonterminal(   "q2");
  symbol_t q3    = g.add_nonterminal(   "q3");

  add(g, list_of(cMSet)(cMSet), cMSet);
  add(g, list_of(q0)(cMSet), q1);
  add(g, list_of(q2)(cMSet), q3);
  add(g, list_of(rNAT)(kNAT), rNAT);
  add(g, list_of(kNAT)(rNAT), rNAT);
  add(g, list_of(kNAT)(kNAT), kNAT);
  
  add1(g, t0, cNat);
  add1(g, t0, cMSet);
  add1(g, t0, kNAT);
  add1(g, t0, q0);

  add1(g, t1, cNat);
  add1(g, t1, cMSet);
  add1(g, t1, kNAT);
  add1(g, t1, q2);

  add1(g, t2, dNat);
  add1(g, t2, dMSet);
  add1(g, t2, kNAT);
  add1(g, t2, rNAT);
    
  parikh_map_t s = g.parikh_image();

  if (s.size() != 10) error("Incorrect size");
  if (s[cNat].dim() != 3) error("Incorrect terminal count");

  if (is_empty(s[cMSet])) error("MSet empty");

  if (s[cMSet].begin()->periods().size() == 0) error("MSet finite");

  typedef parikh_map_t::const_iterator iter;
  for (iter i = s.begin(); i != s.end(); ++i)
    cerr << "set: " << i->first << " " << i->second;
}


int main(int argc, char **argv)
{
  try {
    test_simple();
    return 0;
  } catch (const exception& e) {
    cerr << e.what() << endl;
    return 1;
  }
}
