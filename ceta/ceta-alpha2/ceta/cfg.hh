/* Copyright 2005 Joe Hendrix
 * 
 * Ceta is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 */
#ifndef _cfg_hh_
#define _cfg_hh_

#include <set>
#include <vector>

/** \file
 * Defines a templated definition of a context free grammar with three types
 * of rules -- rules that produce terminals, a single nonterminal, and a 
 * pair of nonterminals.  The data structures have been made generic so that
 * any type may be used as a terminal and nonterminal symbol.  The elements
 * however should follow the rules a map key is suppossed to follow: be
 * copy constructable, comparable, be orderable using std::less, and not to
 * be mutated once added to a data structure.
 */
namespace ceta {
namespace cfg {
  /** A production rule from a nonterminal to a terminal. */
  template<typename Terminal, typename Nonterminal>
  struct trule_t {
    /** Construct a terminal production rule. */
    trule_t(const Nonterminal& lhs_arg, const Terminal& rhs_arg)
      : lhs(lhs_arg),
        rhs(rhs_arg) {
    }
    /** Left-hand side of production rule. */
    Nonterminal lhs;
    /** Right-hand side of production rule. */
    Terminal rhs;
  };
  /** 
   * Helper method for constructing a terminal rule so that most client code
   * does not need to refer to trule_t directly. 
   * \relates trule_t
   */
  template<typename Terminal, typename Nonterminal>
  trule_t<Terminal, Nonterminal>
  make_trule(const Nonterminal& lhs, const Terminal& rhs) {
    return trule_t<Terminal, Nonterminal>(lhs, rhs);
  }

  /** A unary production rule from a nonterminal to another nonterminal. */
  template<typename Nonterminal>
  struct urule_t {
    /** Construct a unary rule. */
    urule_t(const Nonterminal& lhs_arg, const Nonterminal& rhs_arg)
      : lhs(lhs_arg),
        rhs(rhs_arg) {
    }
    /** Left-hand side of production rule. */
    Nonterminal lhs;
    /** Right-hand side of production rule. */
    Nonterminal rhs;
  };
  /** 
   * Helper method for constructing a unary rule so that most client code
   * does not need to refer to urule_t directly. 
   * \relates urule_t
   */
  template<typename Nonterminal>
  urule_t<Nonterminal>
  make_urule(const Nonterminal& lhs, const Nonterminal& rhs) {
    return urule_t<Nonterminal>(lhs, rhs);
  }


  /** 
   * A regular production rule from a nonterminal to two nonterminals.
   * This is a simple read-only data structure and so its members are
   * exposed publically.
   */
  template<typename Nonterminal>
  struct rrule_t {
    /** Construct a regular rule. */
    rrule_t(const Nonterminal& lhs_arg,
            const Nonterminal& rhs1_arg, const Nonterminal& rhs2_arg)
      : lhs(lhs_arg),
        rhs1(rhs1_arg),
        rhs2(rhs2_arg) {
    }

    /** Left-hand side of production rule. */
    Nonterminal lhs;
    /** First nonterminal on right-hand side of production rule. */
    Nonterminal rhs1;
    /** Second nonterminal on reft-hand side of production rule. */
    Nonterminal rhs2;
  };
  
  /** 
   * Helper method for constructing a regular rule so that most client code
   * does not need to refer to rrule_t directly. 
   * \relates rrule_t
   */
  template<typename Nonterminal>
  rrule_t<Nonterminal> make_rrule(const Nonterminal& lhs,
                                  const Nonterminal& rhs1,
                                  const Nonterminal& rhs2) {
    return rrule_t<Nonterminal>(lhs, rhs1, rhs2);
  }

  //TODO: Document members of this class.
  /** A collection of context free production rules. */
  template<typename Terminal, typename Nonterminal>
  class cfg_t {
    typedef std::set<Terminal> terminal_set_t;
    typedef std::set<Nonterminal> nonterminal_set_t;
    typedef std::vector<trule_t<Terminal, Nonterminal> > trule_vector_t;
    typedef std::vector<urule_t<Nonterminal> > urule_vector_t;
    typedef std::vector<rrule_t<Nonterminal> > rrule_vector_t;
  public:
    /** Iterator that points to terminals. */
    typedef typename terminal_set_t::const_iterator terminal_iterator;
    /** Iterator that points to nonterminals. */
    typedef typename nonterminal_set_t::const_iterator nonterminal_iterator;
    /** Iterator that points to terminating production rules. */
    typedef typename trule_vector_t::const_iterator trule_iterator;
    /** Iterator that points to unary production rules. */
    typedef typename urule_vector_t::const_iterator urule_iterator;
    /** Iterator that points to regular production rules. */
    typedef typename rrule_vector_t::const_iterator rrule_iterator;

    /** Add a terminating production rule. */
    void add(const trule_t<Terminal, Nonterminal>& p) {
      nonterminals_.insert(p.lhs);
      terminals_.insert(p.rhs);
      trules_.push_back(p);
    }

    void add_terminal(const Terminal& t) {
      terminals_.insert(t);
    }

    void add_nonterminal(const Nonterminal& nt) {
      nonterminals_.insert(nt);
    }

    /** Add a unary production rule lhs ::= rhs. */
    void add(const Nonterminal& lhs, const Nonterminal& rhs) {
      nonterminals_.insert(lhs);
      nonterminals_.insert(rhs);
      urules_.push_back(urule_t<Nonterminal>(lhs, rhs));
    }

    /** Add a regular production rule. */
    void add(const rrule_t<Nonterminal>& p) {
      nonterminals_.insert(p.lhs);
      nonterminals_.insert(p.rhs1);
      nonterminals_.insert(p.rhs2);
      rrules_.push_back(p);
    }

    /**
     * Return iterator that points to first terminal that appears in a rule
     * added to this cfg.
     */
    terminal_iterator terminals_begin(void) const {
      return terminals_.begin();
    }

    /** 
     * Returns iterator that points one past the last terminal that appears
     * in a rule added to this cfg.
     */
    terminal_iterator terminals_end(void) const {
      return terminals_.end();
    }
    
    /**
     * Return iterator that points to first nonterminal that appears in a
     * rule added to this cfg.
     */
    nonterminal_iterator nonterminals_begin(void) const {
      return nonterminals_.begin();
    }

    /** 
     * Returns iterator that points one past the last nonterminal that
     * appears in a rule added to this cfg.
     */
    nonterminal_iterator nonterminals_end(void) const {
      return nonterminals_.end();
    }

    trule_iterator trules_begin(void) const {
      return trules_.begin();
    }

    trule_iterator trules_end(void) const {
      return trules_.end();
    }

    urule_iterator urules_begin(void) const {
      return urules_.begin();
    }

    urule_iterator urules_end(void) const {
      return urules_.end();
    }

    rrule_iterator rrules_begin(void) const {
      return rrules_.begin();
    }

    rrule_iterator rrules_end(void) const {
      return rrules_.end();
    }
  private:
    terminal_set_t terminals_;
    nonterminal_set_t nonterminals_;
    trule_vector_t trules_;
    urule_vector_t urules_;
    rrule_vector_t rrules_;
  };
}}
#endif
