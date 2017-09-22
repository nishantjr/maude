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

//void add(cfg_t& g, const list<symbol_t>& lhs, symbol_t rhs) {
//  symbol_t lhs_elts[lhs.size()];
//  std::copy(lhs.begin(), lhs.end(), lhs_elts);
//  g.add_transition(lhs_elts, lhs_elts + lhs.size(), rhs);
//}
//
//void add1(cfg_t& g, symbol_t lhs, symbol_t rhs) {
//  g.add_transition(lhs, rhs);
//}

void test_and(void) {
  cfg_t<size_t, string> g;
  size_t t0 = 0; g.add_terminal(t0);
  size_t t1 = 1; g.add_terminal(t1);

  g.add_nonterminal("Term1");
  g.add_nonterminal("Term2");
  g.add_nonterminal("cBool");
  g.add_nonterminal("rBool");

  g.add(rrule_t<string>("rBool", "Term1", "cBool"));
  g.add(rrule_t<string>("rBool", "Term2", "cBool"));
  g.add(trule_t<size_t, string>("Term1", 0));
  g.add(trule_t<size_t, string>("cBool", 0));
  g.add(trule_t<size_t, string>("Term2", 1));
  g.add(trule_t<size_t, string>("cBool", 1));

  typedef std::map<std::string, semilinear_set> parikh_map_t;
  parikh_map_t s = parikh_image(2, g);
}

void test_mset() {
  cfg_t<size_t, string> g;

  size_t t0 = 0; g.add_terminal(t0); // {cNat, cMSet, kNAT, q0}
  size_t t1 = 1; g.add_terminal(t1); // {cNat, cMSet, kNAT, q2}
  size_t t2 = 2; g.add_terminal(t2); // {dNat, dMSet, kNAT, rNAT}

  string cNat  = "cNat";  g.add_nonterminal(cNat); 
  string cMSet = "cMSet"; g.add_nonterminal(cMSet); 
  string dNat  = "dNat";  g.add_nonterminal(dNat); 
  string dMSet = "dMSet"; g.add_nonterminal(dMSet); 
  string rNAT  = "rNAT";  g.add_nonterminal(rNAT); 
  string kNAT  = "kNAT";  g.add_nonterminal(kNAT); 
  string q0    = "q0";    g.add_nonterminal(q0); 
  string q1    = "q1";    g.add_nonterminal(q1); 
  string q2    = "q2";    g.add_nonterminal(q2); 
  string q3    = "q3";    g.add_nonterminal(q3); 

  g.add(make_rrule(cMSet, cMSet, cMSet));
  g.add(make_rrule(q1, q0, cMSet));
  g.add(make_rrule(q3, q2, cMSet));
  g.add(make_rrule(rNAT, rNAT, kNAT));
  g.add(make_rrule(rNAT, kNAT, rNAT));
  g.add(make_rrule(kNAT, kNAT, kNAT));
  
  g.add(make_trule(cNat,  t0));
  g.add(make_trule(cMSet, t0));
  g.add(make_trule(kNAT,  t0));
  g.add(make_trule(q0,    t0));

  g.add(make_trule(cNat,  t1));
  g.add(make_trule(cMSet, t1));
  g.add(make_trule(kNAT,  t1));
  g.add(make_trule(q2,    t1));

  g.add(make_trule(dNat,  t2));
  g.add(make_trule(dMSet, t2));
  g.add(make_trule(kNAT,  t2));
  g.add(make_trule(rNAT,  t2));
    
  typedef std::map<std::string, semilinear_set> parikh_map_t;
  parikh_map_t s = parikh_image(3, g);

  if (s.size() != 10) error("Incorrect size");
  if (s[cNat].dim() != 3) error("Incorrect terminal count");

  if (is_empty(s[cMSet])) error("MSet empty");

  if (s[cMSet].begin()->periods().size() == 0) error("MSet finite");

  typedef parikh_map_t::const_iterator iter;
  for (iter i = s.begin(); i != s.end(); ++i)
    cerr << "set: " << i->first << " " << i->second;
  cerr << endl;
}


int main(int argc, char **argv)
{
  try {
    test_and();
    test_mset();
    return 0;
  } catch (const exception& e) {
    cerr << e.what() << endl;
    return 1;
  }
}
