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
#ifndef _ceta_hh_
#define _ceta_hh_
/** \file
 * \brief
 * Data structures and algorithms for representing and reasoning about
 * propositional tree automata.
 * 
 * ceta.hh provides the data structures and algorithms in the Ceta
 * library for reasoning about propositional tree automaton.  The definitions
 * in this file make it easy for users to define equational theories 
 * over a many-kind signature containing associativity, commutativity, and
 * identity axioms, to define tree automata over such an equational tree 
 * automaton, to efficiently combine tree automata, and to solve many
 * common tree automata decision problems such as emptiness testing and
 * membership.
 *
 * Although the name of this file is "ceta.hh" where the c stands for
 * constrained, in this release, we do not yet support constraints.  The 
 * focus in this release is getting decision procedures for automata without
 * containts over an equaional theory.
 * 
 * There are a number of design decisions that users of this library should
 * be aware of before examining the detailed class and method descriptions
 * below.
 *
 * These classes are not designed to be base classes.  They contain no
 * virtual methods, and in particular a non-virtual destructor.  This means
 * that if a client does derive from one of the classes, the result of
 * destroying the derived class through a base class pointer is undefined.
 * 
 * Instances of ceta::kind_t, ceta::op_t, and ceta::state_t have equivalence
 * semantics similar to that of pointers.  Specifically, each time an
 * instance is created the instance is considered distinct from previously
 * created instances unless the new instance was copy constructed.  For
 * example, the code <code>kind_t k("INT")</code> creates a new kind whose
 * name equal "INT".  In this case, <code>k</code> is distinct from every
 * previously created kind even if the previously created kind is named 
 * <code>"INT"</code> as well.  On the other hand, instances may be copy
 * constructed or assigned the value of a different instance.  In this case,
 * the two instances are considered equal.  Assignment only affects the
 * instance that is assigned to, it does not merge two equivalence classes.
 * For example, if <code>f</code> and <code>g</code> refer to the same
 * operator and <code>h</code> refers to a different operator, then the code
 * <code>f = h</code> makes <code>f</code> equivalent, but does not affect
 * <code>g</code>.  The implementation of these classes uses reference counts
 * and since circular references are impossible, there is no need to worry
 * about garbage collecting these classes.
 *
 * As an aid to using these classes with the STL collection classes,
 * instances of ceta::kind_t, ceta::op_t, and ceta::_state_t are ordered
 * using operator<(), based on heap memory addresses.  This order is not
 * guaranteed to remain consistent between runs, however it is guaranteed to
 * rename consistent during an execution of the program and allows the use of
 * std::less as the ordering for associative collections of kinds, operators,
 * and states.
 *
 * The decision to allow different kinds, operators, and states to have the
 * same name is an intentional design decision.  It avoids the challenges of
 * coming up with a guaranteed unique name for every symbol and maintaining
 * a global name database in multithreaded code.
 *
 * All of the classes in this file use reference counting or contain objects
 * that use reference counting.  This decision was made both for efficiency
 * reasons and to give the previously mentioned equivalence semantics to
 * ceta::kind_t, ceta::op_t, and ceta::state_t.  This can have an impact in
 * multithreaded code.  There are no problems if two threads create instances
 * with no interaction between instances of different threads.  However, if
 * class instances created by one thread are used by class instances of
 * another, then there should be locking to insure that those interactions
 * are thread-safe.  Moreover, if an object is modified or created during
 * such an interaction between two threads, then not only all uses of that 
 * object should be guared by a lock, but all uses of objects previously used
 * to modify or create the object even indirectly.  For example, if kind
 * <code>k</code> is an input kind to an operator, that operator is then 
 * added to a signature which in turn is used to create a tree automaton
 * <code>a</code>, and then <code>a</code> is intersected with a tree
 * automaton created by a different thread, then all accesses to
 * <code>k</code> should be protected by mutual exclusion primitives.  In
 * practice, this means that interactions between class instances created by
 * different threads should be rare, and tightly controlled.
 *
 * We have an extended example for using this header file.  See exampe1.cc
 * in the list of examples generated by Doxygen.
 */

/** \example example1.cc
 * This is an example showing the use of the ceta.hh.  We create a theory and
 * build three different automata using that theory, each extending the
 * other.  Then we perform boolean operations on the languages and test
 * for emptiness.
 */

#include <map>
#include <set>
#include <vector>
#include <iostream>
#include <algorithm>

#include <boost/shared_ptr.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/optional/optional.hpp>
#include <boost/variant.hpp>

#include <ceta/export.h>

/** Namespace for all of Ceta's declarations. */
namespace ceta {
  class kind_impl;

  /** A kind in a many-kinded signature. */
  class CETA_DSO_EXPORT kind_t {
  public:
    /** Constructs a new kind with the given name. */
    explicit kind_t(const std::string& name)
      : name_(new std::string(name)) { 
    }
  private:
    friend const std::string& name(const kind_t& kind);
    /** Pointer to name. */
    boost::shared_ptr<std::string> name_;
  };
  /**
   * Returns name of this kind.
   * \relates kind_t
   */
  inline
  const std::string& name(const kind_t& kind) {
    return *(kind.name_);
  }
  /**
   * Returns true if lhs refers to same kind as rhs.
   * \relates kind_t
   */
  inline
  bool operator==(const kind_t& lhs, const kind_t& rhs) {
    return &name(lhs) == &name(rhs);
  }
  /**
   * Returns true if lhs does not refer to same kind as rhs.
   * \relates kind_t
   */
  inline
  bool operator!=(const kind_t& lhs, const kind_t& rhs) {
    return !(lhs == rhs);
  }
  /**
   * Compares two kinds based on address of kind they point to.
   * \relates kind_t
   */
  inline
  bool operator<(const kind_t& lhs, const kind_t& rhs) {
    return &name(lhs) < &name(rhs);
  }
  /**
   * Writes kind's name to output stream.
   * \relates kind_t
   */
  inline
  std::ostream& operator<<(std::ostream& o, const kind_t& kind) {
    return o << name(kind);
  }

  /** An operator in a many-kinded signature. */
  class CETA_DSO_EXPORT op_t {
  public:
    /** 
     * Type of constant random-access iterator that is used to iterate
     * through the input kinds of an operator.
     */
    typedef std::vector<kind_t>::const_iterator input_iterator;
    /**
     * Constructs a new operator.
     * \param name Name of operator.
     * \param inputs_begin An input iterator that points to first the input
     *                     kind.
     * \param inputs_end  An input iterator that points one past the last
     *                    input kind.
     * \param output Output kind of operator.
     */
    template<typename InputIterator>
    op_t(const std::string& name, InputIterator inputs_begin,
         InputIterator inputs_end, const kind_t& output) 
      : impl_(new impl_t(name,
                         std::vector<kind_t>(inputs_begin, inputs_end),
                         output)) {
    }
  private:
    friend const std::string& name(const op_t& op);
    friend const op_t::input_iterator inputs_begin(const op_t& op);
    friend const op_t::input_iterator inputs_end(const op_t& op);
    friend const kind_t& output(const op_t& op);
    friend bool operator==(const op_t& lhs, const op_t& rhs);
    friend bool operator<( const op_t& lhs, const op_t& rhs);
    /** Implementation type. */
    typedef boost::tuple<std::string, std::vector<kind_t>, kind_t> impl_t;
    /** Pointer to implementation. */
    boost::shared_ptr<impl_t> impl_;
  };
  /**
   * Returns the name of this operator.
   * \relates op_t
   */
  inline
  const std::string& name(const op_t& op) {
    return op.impl_->get<0>();
  }
  /**
   * Returns iterator that points to first input kind of the operator.
   * \relates op_t
   */
  inline
  const op_t::input_iterator inputs_begin(const op_t& op) {
    return op.impl_->get<1>().begin();
  }
  /**
   * Returns iterator that points one past the last input kind of the
   * operator.
   * \relates op_t
   */
  inline
  const op_t::input_iterator inputs_end(const op_t& op) {
    return op.impl_->get<1>().end();
  }
  /**
   * Returns the output kind of this operator.
   * \relates op_t
   */
  inline
  const kind_t& output(const op_t& op) {
    return op.impl_->get<2>();
  }
  /**
   * Returns true if this is the same operator as rhs.
   * \relates op_t
   */
  inline
  bool operator==(const op_t& lhs, const op_t& rhs) {
    return lhs.impl_ == rhs.impl_;
  }
  /**
   * Compares two operators based on address of implementation.
   * \relates op_t
   */
  inline
  bool operator<(const op_t& lhs, const op_t& rhs) {
    return lhs.impl_ < rhs.impl_;
  }
  /**
   * Returns true if lhs does not equal rhs.
   * \relates op_t
   */
  inline
  bool operator!=(const op_t& lhs, const op_t& rhs) {
    return !(lhs == rhs);
  }
  /**
   * Returns the ith input kind for operator.
   * \relates op_t
   */
  inline
  const kind_t& input(const op_t& op, size_t i) {
    return inputs_begin(op)[i];
  }
  /**
   * Returns number of inputs for operator.
   * \relates op_t
   */
  inline
  size_t input_count(const op_t& op) {
    return std::distance(inputs_begin(op), inputs_end(op));
  }
  /**
   * Returns true if op is a constant.
   * \relates op_t
   */
  inline
  bool is_constant(const op_t& op) {
    return inputs_begin(op) == inputs_end(op);
  }
  /**
   * Returns true if op takes two args with same kind as output kind.
   * \relates op_t
   */
  inline
  bool is_binary(const op_t& op) {
    return (input_count(op) == 2)
        && (input(op, 0) == output(op))
        && (input(op, 1) == output(op));
  }
  /**
   * Constructs a constant operator.
   * \relates op_t
   */
  inline
  op_t make_constant(const std::string& name, const kind_t& output) {
    const kind_t* end = NULL;
    return op_t(name, end, end, output);
  }
  /**
   * Constructs a unary operator.
   * \relates op_t
   */
  inline
  op_t make_unary_op(const std::string& name, const kind_t& input1,
                     const kind_t& output) {
    const kind_t inputs[] = { input1, };
    return op_t(name, inputs, inputs + 1, output);
  }
  /**
   * Constructs a binary operator.
   * \relates op_t
   */
  inline
  op_t make_binary_op(const std::string& name,
                      const kind_t& input1, const kind_t& input2,
                      const kind_t& output) {
    const kind_t inputs[] = { input1, input2 };
    return op_t(name, inputs, inputs + 2, output);
  }
  /**
   * Writes the operator's identifier to the output stream.
   * \relates op_t
   */
  inline
  std::ostream& operator<<(std::ostream& o, const op_t& op) {
    return o << name(op);
  }

  class term_t;

  /** \internal
   * Checks that term is a constant.
   * \relates term_t
   */
  void check_constant(const op_t& term) CETA_DSO_EXPORT;
  /** \internal
   * Checks that kinds are equal.
   * \relates term_t
   */
  void check_equal(const kind_t& kind, const kind_t& kind) CETA_DSO_EXPORT;
  /** \internal
   * Checks that a term with given operator and subterms would be well
   * formed.
   * \relates term_t
   */
  void check_well_formed(const op_t& op,
                         const std::vector<term_t>& subterms) CETA_DSO_EXPORT;
  /** 
   * A term built from operators in a many-kinded signature.  Instances of
   * this class may be in partially flattened form.  That is binary symbols
   * may contain more than two subterms.  */
  class CETA_DSO_EXPORT term_t {
  public:
    /** 
     * Type of constant random-access iterator that is used to iterate
     * through the kinds in a theory.
     */
    typedef std::vector<term_t>::const_iterator subterm_iterator;
    /**
     * Constructs a new term.  If the subterms are not valid subterms for
     * this operator, then an exception may be thrown, however this is only
     * to aid client debugging, and should not be depended upon in production
     * code.
     *
     * \param op Top operator of term.
     * \param subterms_begin An input iterator that points to first subterm.
     * \param subterms_end  An input iterator that points one past the last
     *        subterm.
     */
    template<typename I>
    term_t(const op_t& op, I subterms_begin, I subterms_end)
      : impl_(new impl_t(op, std::vector<term_t>(subterms_begin,
                                                 subterms_end))) {
      check_well_formed(op, impl_->get<1>());
    }
  private:
    friend const op_t& op(const term_t& term);
    friend term_t::subterm_iterator subterms_begin(const term_t& term);
    friend term_t::subterm_iterator subterms_end(const term_t& term);
    /** Implementation type. */
    typedef boost::tuple<op_t, std::vector<term_t> > impl_t;
    /** Pointer to implementation. */
    boost::shared_ptr<impl_t> impl_;
  };
  /**
   * Returns operator at the top of this term.
   * \relates term_t
   */
  inline
  const op_t& op(const term_t& term) {
    return term.impl_->get<0>();
  }
  /**
   * Returns iterator that points to first subterm of the term.
   * \relates term_t
   */
  inline
  term_t::subterm_iterator subterms_begin(const term_t& term) {
    return term.impl_->get<1>().begin();
  }
  /**
   * Returns iterator that points one past the last subterm of the term.
   * \relates term_t
   */
  inline
  term_t::subterm_iterator subterms_end(const term_t& term) {
    return term.impl_->get<1>().end();
  }
  /** 
   * Constructs a constant term with the given operator with must be a
   * constant symbol.
   * \relates term_t
   */
  inline
  term_t make_constant(const op_t& op) {
    const term_t* end = NULL;
    return term_t(op, end, end);
  }
  /**
   * Returns number of subterms of term.
   * \relates term_t
   */
  inline
  size_t subterm_count(const term_t& term) {
    return subterms_end(term) - subterms_begin(term);
  }
  /**
   * Returns the ith subterm of the term.
   * \relates term_t
   */
  inline
  const term_t& subterm(const term_t& term, size_t i) {
    return subterms_begin(term)[i];
  }
  /**
   * Returns kind of term.
   * \relates term_t
   */
  inline
  const kind_t& kind(const term_t& term) {
    return output(op(term));
  }
  /**
   * Returns true if term is a contant.
   * \relates term_t
   */
  inline
  bool is_constant(const term_t& term) {
    return subterms_begin(term) == subterms_end(term);
  }
  /**
   * Writes term to output stream.
   * \relates term_t
   */
  std::ostream&
        operator<<(std::ostream& o, const term_t& term) CETA_DSO_EXPORT;

  /** Type of identity for binary operator. */
  enum id_type_t { 
    id_none,  ///< Operator has no identity.
    id_left,  ///< Operator has left identity.
    id_right, ///< Operator has right identity.
    id_both   ///< Operator has identity.
  };

  class theory_impl;

  /**
   * An axiom set is a set of axioms for an operator in a theory which may
   * include axioms for associativity, commutativity, and identity.
   *
   * This class is not constructable directly.  Instead singleton sets can be
   * constructed using none(), assoc(), comm(), left_id(), right_id(), id(),
   * and then combined using operator|() and operator|=().  For example,
   * the expression <code>assoc() | comm() | id(c)</code> constructs a set of
   * axioms for an associative and commutative symbol with an identity 
   * <code>c</code>, 
   */
  class axiom_set_t {
  public:
    /** Adds attributes from rhs to these attributes. */
    axiom_set_t& operator|=(const axiom_set_t& rhs);
  private:
    friend bool is_assoc(const axiom_set_t& axiom);
    friend bool is_comm(const axiom_set_t& axiom);
    friend id_type_t id_type(const axiom_set_t& axiom);
    friend const boost::optional<op_t>& id_symbol(const axiom_set_t& axiom);
    friend const axiom_set_t& none();
    friend const axiom_set_t& assoc();
    friend const axiom_set_t& comm();
    friend const axiom_set_t left_id(const op_t& id);
    friend const axiom_set_t right_id(const op_t& id);
    friend const axiom_set_t id(const op_t& id);
    /** Creates a new axiom set. */
    axiom_set_t(bool is_assoc, bool is_comm, id_type_t id_type = id_none,
                const boost::optional<op_t>& id_symbol 
                    = boost::optional<op_t>())
      : is_assoc_(is_assoc),
        is_comm_(is_comm),
        id_type_(id_type),
        id_symbol_(id_symbol) {
    }
    bool is_assoc_;
    bool is_comm_;
    id_type_t id_type_;
    boost::optional<op_t> id_symbol_;
  };
  /** 
   * Returns true if attributes contain associativity.
   * \relates axiom_set_t
   */
  inline
  bool is_assoc(const axiom_set_t& axiom) {
    return axiom.is_assoc_;
  }
  /**
   * Returns true if attributes contain commutativity.
   * \relates axiom_set_t
   */
  inline
  bool is_comm(const axiom_set_t& axiom) {
    return axiom.is_comm_;
  }
  /**
   * Returns type of identity for these attributes.
   * \relates axiom_set_t
   */
  inline
  id_type_t id_type(const axiom_set_t& axiom) {
    return axiom.id_type_;
  }
  /** 
   * Returns identity for these attributes if there is one.
   * \relates axiom_set_t
   */
  inline
  const boost::optional<op_t>& id_symbol(const axiom_set_t& axiom) {
    return axiom.id_symbol_;
  }
  /** 
   * Returns set containing no axioms.
   * \relates axiom_set_t
   */
  inline
  const axiom_set_t& none() {
    static axiom_set_t r(false, false);
    return r;
  }
  /**
   * Returns set only containing associative axiom.
   * \relates axiom_set_t
   */
  inline
  const axiom_set_t& assoc() {
    static axiom_set_t r(true, false);
    return r;
  }
  /**
   * Returns set only containing commutativity axiom.
   * \relates axiom_set_t
   */
  inline
  const axiom_set_t& comm() {
    static axiom_set_t r(false, true);
    return r;
  }
  /**
   * Returns set only containing left identity axiom.
   * \relates axiom_set_t
   */
  inline
  const axiom_set_t left_id(const op_t& id) {
    check_constant(id);
    return axiom_set_t(false, false, id_left, id);
  }
  /**
   * Returns set only containing right identity axiom.
   * \relates axiom_set_t
   */
  inline
  const axiom_set_t right_id(const op_t& id) {
    check_constant(id);
    return axiom_set_t(false, false, id_right, id);
  }
  /**
   * Returns set only containing left and right identity axioms.
   * \relates axiom_set_t
   */
  inline
  const axiom_set_t id(const op_t& id) {
    check_constant(id);
    return axiom_set_t(false, false, id_both, id);
  }
  /**
   * Returns true if the two axiom sets are equal.
   * \relates axiom_set_t
   */
  inline
  bool operator==(const axiom_set_t& x, const axiom_set_t& y) {
    return ( is_assoc(x) == is_assoc(y))
        && (  is_comm(x) == is_comm(y))
        && (  id_type(x) == id_type(y))
        && (id_symbol(x) == id_symbol(y));
  }
  /**
   * Returns true if the two axiom sets are not equal.
   * \relates axiom_set_t
   */
  inline
  bool operator!=(const axiom_set_t& x, const axiom_set_t& y) {
    return !(x == y);
  }
  /**
   * Returns union of two axiom sets.
   * \relates axiom_set_t
   */
  inline
  const axiom_set_t operator|(const axiom_set_t& x, const axiom_set_t& y) {
    return axiom_set_t(x) |= y;
  }
  
  /** 
   * An equational theory over a many-kind signature.
   *
   * Each theory is a data structure containing an ordered collection of
   * kinds, an ordered collection of operators whose domain and range is
   * specified in terms of those kinds, and equations involving the
   * operators.  Currently, the equations can be associativity,
   * commutativity, or identity axioms, and arbitrary equations are not
   * allowed.  We allow left-identity and right-identity axioms if a symbol
   * is neither associative or commutative, however one-way identities are
   * not allowed if the binary symbol is associative or commutative.
   * Additionally, identity terms must be constants, and a binary operator
   * may contain at most one identity.
   *
   * If a programmer attempts to violate these constraints, an exception may
   * be thrown, however this behavior should not be relied upon.  The 
   * exception is only there to aid client debugging.
   *
   * Iterators to kinds and operators returned by instances of this class
   * are guaranteed to iterate over their elements in order.  Due to the 
   * the implementation using reference counting and copy-on-write semantics,
   * iterators are not guaranteed to remain valid after the theory is
   * modified.
   */
  class theory_t {
    friend class axiom_set_proxy_t;
  public:
    /** 
     * Type of constant bidirectional iterator that is used to iterate
     * through the kinds in a theory.  Iterators may be invalidated if the
     * automaton is modified.
     */
    typedef std::set<kind_t>::const_iterator kind_iterator;
    /**
     * Type of constant bidirectional iterator that is used to iterate
     * through the operators in a theory.  Iterators may be invalidated if
     * the automaton is modified.
     */
    typedef std::set<op_t>::const_iterator op_iterator;

    /** Constructs an empty equational theory. */
    theory_t();
  private:
    friend const kind_iterator add_kind(theory_t& theory,
                                        const kind_t& kind);
    friend const op_iterator add_op(theory_t& theory, const op_t& op);
    friend void  set_axioms(theory_t& theory, const op_t& bin_op,
                            const axiom_set_t& axioms);
    friend const axiom_set_t& axioms(const theory_t& theory, const op_t& op);
    friend theory_t::kind_iterator kinds_begin(const theory_t& theory);
    friend theory_t::kind_iterator kinds_end(const theory_t& theory);
    friend bool member(const theory_t& theory, const kind_t& kind);
    friend bool member(const theory_t& theory, const op_t& op);
    friend theory_t::op_iterator ops_begin(const theory_t& theory);
    friend theory_t::op_iterator ops_end(const theory_t& theory);
    friend bool operator==(const theory_t& x, const theory_t& y);
    friend theory_t::op_iterator id_contexts_begin(
            const theory_t& theory, const op_t& id_symbol);
    friend theory_t::op_iterator id_contexts_end(
            const theory_t& theory, const op_t& id_symbol);
    friend bool is_identity(const theory_t& theory, const op_t& id_symbol);
    /** Pointer to implementation. */
    boost::shared_ptr<theory_impl> impl_;
  };
  /**
   * Returns set of axioms for operator.
   * \relates theory_t
   */
  const axiom_set_t&
    axioms(const theory_t& theory, const op_t& op) CETA_DSO_EXPORT;
  /**
   * Returns iterator that points to first kind in the theory.
   * \relates theory_t
   */
  theory_t::kind_iterator kinds_begin(const theory_t& theory) CETA_DSO_EXPORT;
  /**
   * Returns iterator that points one past the last kind in the theory.
   * \relates theory_t
   */
  theory_t::kind_iterator kinds_end(const theory_t& theory) CETA_DSO_EXPORT;
  /**
   * Returns true if kind is in the theory.
   * \relates theory_t
   */
  bool member(const theory_t& theory, const kind_t& kind) CETA_DSO_EXPORT;
  /**
   * Returns true if operator is in the theory.
   * \relates theory_t
   */
  bool member(const theory_t& theory, const op_t& op) CETA_DSO_EXPORT;
  /**
   * Returns iterator that points to the first operator in the theory.
   * \relates theory_t
   */
  theory_t::op_iterator ops_begin(const theory_t& theory) CETA_DSO_EXPORT;
  /**
   * Returns iterator that points one past the last operator in the theory.
   * \relates theory_t
   */
  theory_t::op_iterator ops_end(const theory_t& theory) CETA_DSO_EXPORT;
  /**
   * Returns iterator that points to the first binary operator that has an
   * identity id_symbol in the theory.
   * \relates theory_t
   */
  theory_t::op_iterator id_contexts_begin(
          const theory_t& theory, const op_t& id_symbol) CETA_DSO_EXPORT;
  /**
   * Returns iterator that points one past the last binary operator that
   * has an identity id_symbol in the theory.
   * \relates theory_t
   */
  theory_t::op_iterator id_contexts_end(
          const theory_t& theory, const op_t& id_symbol) CETA_DSO_EXPORT;
  /**
   * Returns true if symbol is an identity for some binary symbol in theory
   * \relates theory_t
   */
  inline
  bool is_identity(const theory_t& theory, const op_t& id_symbol) {
    return id_contexts_begin(theory, id_symbol) 
        == id_contexts_end(theory, id_symbol);
  }
  /**
   * Adds kind to theory.
   * \relates theory_t
   */
  const theory_t::kind_iterator add_kind(theory_t& theory,
                                         const kind_t& kind);
  /** 
   * Adds operator to theory.
   * \relates theory_t
   */
  const theory_t::op_iterator add_op(theory_t& theory, const op_t& op);
  /**
   * Sets axioms for a binary operator.
   * \relates theory_t
   */
  void set_axioms(theory_t& theory, const op_t& bin_op,
                  const axiom_set_t& axioms) CETA_DSO_EXPORT;
  /**
   * Adds additional axioms to axioms for a binary operator.
   * \relates theory_t
   */
  inline
  void add_axioms(theory_t& theory, const op_t& bin_op,
                  const axiom_set_t& new_axioms) {
    set_axioms(theory, bin_op, axioms(theory, bin_op) | new_axioms);
  }
  /**
   * Returns true if two theories are equal.
   * \relates theory_t
   */
  bool operator==(const theory_t& x, const theory_t& y) CETA_DSO_EXPORT;
  /** 
   * Returns true if theories are not equal. 
   * \relates theory_t 
   */
  inline
  bool operator!=(const theory_t& lhs, const theory_t& rhs) {
    return !(lhs == rhs);
  }
  /**
   * Writes theory representation to stream for debugging purposes.
   * \relates theory_t
   */
  std::ostream& operator<<(std::ostream& o,
                           const theory_t& theory) CETA_DSO_EXPORT;

  /** A state in a tree automaton. */
  class CETA_DSO_EXPORT state_t {
  public:
    /** Constructs a new state. */
    state_t(const kind_t& kind, const std::string& name)
      : impl_(new impl_t(kind, name)) {
    }
  private:
    friend const kind_t& kind(const state_t& state);
    friend const std::string& name(const state_t& state);
    friend bool operator==(const state_t& lhs, const state_t& rhs);
    friend bool operator<(const state_t& lhs, const state_t& rhs);
    /** Implementation type. */
    typedef boost::tuple<kind_t, std::string> impl_t;
    /** Pointer to implementation. */
    boost::shared_ptr<impl_t> impl_;
  };
  /** 
   * Returns the kind of this state.
   * \relates state_t
   */
  inline
  const kind_t& kind(const state_t& state) {
    return state.impl_->get<0>();
  }
  /**
   * Returns the name of this state.
   * \relates state_t
   */
  inline
  const std::string& name(const state_t& state) {
    return state.impl_->get<1>();
  }
  /**
   * Returns true if lhs equals rhs.
   * \relates state_t 
   */
  inline
  bool operator==(const state_t& lhs, const state_t& rhs) {
    return lhs.impl_ == rhs.impl_;
  }
  /**
   * Compares states based on address of implementation.
   * \relates state_t
   */
  inline
  bool operator<(const state_t& lhs, const state_t& rhs) {
    return lhs.impl_ < rhs.impl_;
  }
  /**
   * Returns true if lhs does not equal rhs.
   * \relates state_t
   */
  inline
  bool operator!=(const state_t& lhs, const state_t& rhs) {
    return !(lhs == rhs);
  }
  /**
   * Writes the state's name to the output stream.
   * \relates state_t
   */
  inline
  std::ostream& operator<<(std::ostream& o, const state_t& state) {
    return o << name(state);
  }
  /**
   * Writes a set of states to the output stream.
   * \relates state_t
   */
  inline
  std::ostream& operator<<(std::ostream& o, const std::set<state_t>& s) {
    o << "{";
    typedef std::set<state_t>::const_iterator set_iter;
    set_iter i = s.begin();
    set_iter end = s.end();
    if (i != end) {
      o << *(i++);
      while (i != end)
        o << ", " << *(i++);
    }
    return o << "}";
  }

  /** \internal
   * Checks that every state in set has given kind.
   */
  void check_kinds(const kind_t& kind,
                   const std::set<state_t>& states) CETA_DSO_EXPORT;
  
  /**
   * Provides information about the result of testing the property of the
   * language accepted by a tree automaton.
   */
  class CETA_DSO_EXPORT test_result_t {
  public:
    typedef std::set<state_t> set_t;
    /** Constructs result indicating property is satisified. */
    test_result_t() {
    }
    /**
     * Constructs result indicating property is not satisified and provided
     * term as a counterexample.
     */
    test_result_t(const term_t& term, const set_t& set)
      : impl_(make_pair(term, set)) {
      check_kinds(kind(term), set);
    }
    /**
     * Converts result to a boolean that is true if the property is
     * satisfied.
     */
    operator bool() {
      return !impl_;
    }
  private:
    friend const term_t& counterexample(const test_result_t& result);
    friend const set_t& reachable_set(const test_result_t& result);
    /** Pointer to accepted term or null if the property is satisfied. */
    boost::optional< std::pair<term_t, set_t> > impl_;
  };
  /**
   * Returns counterexample of property.
   * \relates test_result_t
   */
  inline
  const term_t& counterexample(const test_result_t& result) {
    return result.impl_->first;
  }
  /**
   * Returns reachable set of counterexample.
   * \relates test_result_t
   */
  inline
  const test_result_t::set_t& reachable_set(const test_result_t& result) {
    return result.impl_->second;
  }
  /** Not operator for predicates. */
  struct not_predicate_t;
  /** And operator for predicates. */
  struct and_predicate_t;
  /** Or operator for predicates. */
  struct or_predicate_t;
  /** A boolean predicate whose models are sets of state symbols. */
  class CETA_DSO_EXPORT state_predicate_t {
  public:
    /**
     * Creates a predicate that returns value for every set of states with
     * given kind.
     */
    state_predicate_t(const kind_t& kind, bool value);
    /** Creates a state predicate whose models are sets containing state. */
    state_predicate_t(state_t state);
  private:
    typedef boost::variant<bool, state_t, not_predicate_t, and_predicate_t,
            or_predicate_t> variant_t;
    typedef boost::tuple<kind_t, variant_t> impl_t;
    friend const state_predicate_t
            operator!(const state_predicate_t& pred);
    friend const state_predicate_t
            operator&(const state_predicate_t& x,
                      const state_predicate_t& y);
    friend const state_predicate_t
            operator|(const state_predicate_t& x,
                      const state_predicate_t& y);
    friend const kind_t& kind(const state_predicate_t& pred);
    template<typename Visitor>
    friend
    typename Visitor::result_type
      apply_visitor(const Visitor& visitor, const state_predicate_t& pred);
    /** Constructs a new predicate given its kind and variant. */
    state_predicate_t(const kind_t& kind, const variant_t& variant);

    /** Implementation of predicate. */
    boost::shared_ptr<impl_t> impl_;
  };
  /** Not operator that complements a predicate. */
  struct not_predicate_t {
    /** Constructs new not predicate. */
    not_predicate_t(const state_predicate_t& new_arg)
      : arg(new_arg) {
    }
    /** Predicate that is complemented by this operator. */
    state_predicate_t arg;
  };
  /** And operator that conjoins two predicates. */
  struct and_predicate_t {
    /** Constructs new and predicate. */
    and_predicate_t(const state_predicate_t& new_lhs,
                    const state_predicate_t& new_rhs)
      : lhs(new_lhs), rhs(new_rhs) {
    }
    /** First predicate that is conjoined by this predicate. */
    state_predicate_t lhs;
    /** Second predicate that is conjoined by this predicate. */
    state_predicate_t rhs;
  };
  /** Or operator that disjoins two predicates.  */
  struct or_predicate_t {
    or_predicate_t(const state_predicate_t& new_lhs,
                   const state_predicate_t& new_rhs)
      : lhs(new_lhs), rhs(new_rhs) {
    }
    /** First predicate that is disjoined by this predicate. */
    state_predicate_t lhs;
    /** Second predicate that is disjoined by this predicate. */
    state_predicate_t rhs;
  };
  /**
   * Creates a predicate that returns value for every set of states with
   * given kind.
   */
  inline
  state_predicate_t::state_predicate_t(const kind_t& kind, bool value)
    : impl_(new impl_t(kind, value)) {
  }
  inline
  /** Creates a state predicate whose models are sets containing state. */
  state_predicate_t::state_predicate_t(state_t state)
    : impl_(new impl_t(kind(state), state)) {
  }
  /** Constructs a new predicate given its kind and variant. */
  inline
  state_predicate_t::state_predicate_t(const kind_t& kind,
          const state_predicate_t::variant_t& variant) 
    : impl_(new impl_t(kind, variant)) {
  }
  /**
   * Returns the kind of the predicate.
   * \relates state_predicate_t
   */
  inline
  const kind_t& kind(const state_predicate_t& pred) {
    return pred.impl_->get<0>();
  }
  template<typename Visitor>
  typename Visitor::result_type
    apply_visitor(const Visitor& visitor, const state_predicate_t& pred) {
    return boost::apply_visitor(visitor, pred.impl_->get<1>());
  }
  /** 
   * Returns complement of predicate.
   * \relates state_predicate_t
   */
  inline
  const state_predicate_t operator!(const state_predicate_t& pred) {
    return state_predicate_t(kind(pred), not_predicate_t(pred));
  }
  /**
   * Returns conjunction of two predicates.
   * \relates state_predicate_t
   */
  inline
  const state_predicate_t operator&(const state_predicate_t& lhs,
                                    const state_predicate_t& rhs) {
    check_equal(kind(lhs), kind(rhs));
    return state_predicate_t(kind(lhs), and_predicate_t(lhs, rhs));
  }
  /**
   * Returns disjunction of two predicates.
   * \relates state_predicate_t
   */
  inline
  const state_predicate_t operator|(const state_predicate_t& lhs,
                                    const state_predicate_t& rhs) {
    check_equal(kind(lhs), kind(rhs));
    return state_predicate_t(kind(lhs), or_predicate_t(lhs, rhs));
  }
  /**
   * Intersects lhs predicate with rhs.
   * \relates state_predicate_t
   */
  inline
  state_predicate_t& operator&=(state_predicate_t& lhs,
                          const state_predicate_t& rhs) {
    return lhs = lhs & rhs;
  }
  /**
   * Unions lhs predicate with rhs.
   * \relates state_predicate_t
   */
  inline
  state_predicate_t& operator|=(state_predicate_t& lhs,
                          const state_predicate_t& rhs) {
    return lhs = lhs | rhs;
  }
  /** 
   * Returns true if set if a model of predicate.
   * \relates state_predicate_t
   */
  bool models(const state_predicate_t& pred,
              const std::set<state_t>& model) CETA_DSO_EXPORT;
  /**
   * Writes predicate to stream for debugging purposes.
   * \relates state_predicate_t
   */
  std::ostream&
    operator<<(std::ostream& o, const state_predicate_t& p) CETA_DSO_EXPORT;

  /** An epsilon rule p -> q. */
  class CETA_DSO_EXPORT erule_t {
  public:
    /** Constructs epsilon rule lhs -> rhs. */
    erule_t(const state_t& lhs, const state_t& rhs)
      : lhs_(lhs),
        rhs_(rhs) {
      check_equal(kind(lhs), kind(rhs));
    }
  private:
    friend const state_t& lhs(const erule_t& erule);
    friend const state_t& rhs(const erule_t& erule);
    /** left-hand side of rule. */
    state_t lhs_;
    /** right-hand side of rule. */
    state_t rhs_;
  };
  /** 
   * Returns left-hand side of rule.
   * \relates erule_t
   */
  inline
  const state_t& lhs(const erule_t& erule) {
    return erule.lhs_;
  }
  /**
   * Returns right-hand side of rule.
   * \relates erule_t
   */
  inline
  const state_t& rhs(const erule_t& erule) {
    return erule.rhs_;
  }
  /**
   * Returns true if x equals y.
   * \relates erule_t
   */
  inline
  bool operator==(const erule_t& x, const erule_t& y) {
    return (lhs(x) == lhs(y)) && (rhs(x) == rhs(y));
  }
  /**
   * Returns true if lhs does not equal rhs.
   * \relates erule_t
   */
  inline
  bool operator!=(const erule_t& lhs, const erule_t& rhs) {
    return !(lhs == rhs);
  }
  /**
   * Returns true if x is less than y.
   * \relates erule_t
   */
  inline
  bool operator<(const erule_t& x, const erule_t& y) {
    return (lhs(x) <  lhs(y))
        || (lhs(x) == lhs(y)) && (rhs(x) < rhs(y));
  }

  void check_well_formed(const op_t& op,
                         const std::vector<state_t>& lhs_states,
                         const state_t& rhs) CETA_DSO_EXPORT;
  /// A rule f(p1, ..., pn) -> q.  
  /**
   * The kind of q should equal the output kind of f.  If f is a binary
   * operator, there must be at least two states on the left-hand-side and
   * their kinds should equal the kinds of the operator.  If f is not binary,
   * then the number of states on the left-hand-side should equal the number
   * of inputs on the operator, and the kind of the ith state should equal
   * the ith input kind of f.
   */
  class CETA_DSO_EXPORT rule_t {
  public:
    /**
     * Type of constant random-access-iterator that can be used to iterate
     * through the left-hand-side states of a rule.
     */
    typedef std::vector<state_t>::const_iterator lhs_state_iterator;
    /**
     * Constructs a new rule.
     * \param op The operator on left-hand-side of rule.
     * \param lhs_states_begin An input iterator that points to the first
     *      state on the left-hand-side of the rule.
     * \param lhs_states_end  An input iterator that points one past the last
     *      state on the left-hand-side of the rule.
     * \param rhs The state on the right-hand-side of the rule.
     */
    template <typename InputIterator>
    rule_t(const op_t& op, InputIterator lhs_states_begin,
           InputIterator lhs_states_end, const state_t& rhs)
      : op_(op),
        lhs_states_(lhs_states_begin, lhs_states_end),
        rhs_(rhs) {
      check_well_formed(op, lhs_states_, rhs);
    }
  private:
    friend const op_t& op(const rule_t& rule);
    friend const lhs_state_iterator lhs_states_begin(const rule_t& rule);
    friend const lhs_state_iterator lhs_states_end(const rule_t& rule);
    friend const state_t& rhs(const rule_t& rule);
    friend bool operator==(const rule_t& lhs, const rule_t& rhs);
    friend bool operator<(const rule_t& lhs, const rule_t& rhs);
    /** Operator on left-hand side of rule. */
    op_t op_;
    /** States on left-hand side of rule. */
    std::vector<state_t> lhs_states_;
    /** State on right-hand side of rule. */
    state_t rhs_;
  };
  /**
   * Returns the operator on left-hand side of rule.
   * \relates rule_t
   */
  inline
  const op_t& op(const rule_t& rule)  {
    return rule.op_;
  }
  /**
   * Returns an iterator that points to first state on the left-hand-side of
   * the rule.
   * \relates rule_t
   */
  inline
  const rule_t::lhs_state_iterator lhs_states_begin(const rule_t& rule) {
    return rule.lhs_states_.begin();
  }
  /**
   * Returns an iterator that points one past the last state on the 
   * left-hand-side of the rule.
   * \relates rule_t
   */
  inline
  const rule_t::lhs_state_iterator lhs_states_end(const rule_t& rule) {
    return rule.lhs_states_.end();
  }
  /**
   * Returns the right-hand side of rule.
   * \relates rule_t
   */
  inline
  const state_t& rhs(const rule_t& rule) {
    return rule.rhs_;
  }
  /**
   * Returns true if x equals y.
   * \relates rule_t
   */
  inline
  bool operator==(const rule_t& x, const rule_t& y) {
    return (op(x) == op(x))
        && (x.lhs_states_ == y.lhs_states_)
        && (rhs(x) == rhs(y));
  }
  /**
   * Returns true if lhs does not equal rhs.
   * \relates rule_t
   */
  inline
  bool operator!=(const rule_t& lhs, const rule_t& rhs) {
    return !(lhs == rhs);
  }
  /**
   * Returns true if lhs is less than rhs.
   * \relates rule_t
   */
  inline
  bool operator<(const rule_t& x, const rule_t& y) {
    return (op(x)  < op(y))
        || (op(x) == op(y)) && (rhs(x)  < rhs(y))
        || (op(x) == op(y)) && (rhs(x) == rhs(y)) 
                            && (x.lhs_states_ < y.lhs_states_);
  }
  /**
   * Returns the state with index i on the left-hand-side of the rule.
   * \param rule A rule.
   * \param i An index in the range 0 <= i < lhs_state_count(i)
   * \relates rule_t
   */
  inline
  const state_t& lhs_state(const rule_t& rule, size_t i) {
    return lhs_states_begin(rule)[i];
  }
  /**
   * Returns number of states on the left-hand-side of the rule.
   * \relates rule_t
   */
  inline
  size_t lhs_state_count(const rule_t& rule) {
    return std::distance(lhs_states_begin(rule), lhs_states_end(rule));
  }
  /**
   * Constructs a rule for a constant symbol.
   * \relates op_t
   */
  inline
  rule_t make_constant_rule(const op_t& lhs_op, const state_t& rhs) {
    const state_t* lhs_states = NULL;
    return rule_t(lhs_op, lhs_states, lhs_states, rhs);
  }
  /**
   * Constructs a rule for a unary symbol.
   * \relates op_t
   */
  inline
  rule_t make_unary_rule(const op_t& lhs_op, const state_t& lhs,
                         const state_t& rhs) {
    return rule_t(lhs_op, &lhs, &lhs + 1, rhs);
  }
  /**
   * Constructs a rule for a binary symbol.
   * \relates op_t
   */
  inline
  rule_t make_binary_rule(const op_t& lhs_op, const state_t& lhs1,
                          const state_t& lhs2, const state_t& rhs) {
    const state_t lhs_states[] = { lhs1, lhs2 };
    return rule_t(lhs_op, lhs_states, lhs_states + 2, rhs);
  }

  class ta_impl;

  /** 
   * \brief An propositional tree automaton over an equational theory.
   *
   * Each automaton is a datastructure that stores the equational theory it
   * is over, an ordered collection of states for each kind, a boolean
   * predicate over those states for each kind, and a collection of epsilon
   * and regular transition rules.  Although, an automaton is a data
   * structure for storing that information, its primary purpose is not to
   * serve as a special purpose collections object, but rather to allow
   * clients to efficiently reason about the language the automaton
   * represents.  Because of this, the states, predicates, and rules in the
   * automaton may not exactly correspond to what was added.  We guarantee
   * that every state added to the automaton will not be removed, that the
   * models containing each added states for each state predicate will remain
   * unchanged, and that the a user-added state is reachable from a term by
   * the automaton if and only if it the state is reachable from a term by
   * the exact automaton specified by the client.  In particular, the
   * automaton may contain additional states that were not added by the
   * client, and the rules may not match what the client added.  
   *
   * The iterators returned by ta_t::states_begin and ta_t::states_end are
   * guaranteed to iterate over the states in order.
   */
  class CETA_DSO_EXPORT ta_t {
  public:
    /** 
     * Type of constant bidirectional iterator that is used to iterate 
     * through the states in an automaton.  Iterators may be invalidated if
     * the automaton is modified.
     */
    typedef std::set<state_t>::const_iterator state_iterator;
    /** 
     * Type of constant bidirectional iterator that is used to iterate 
     * through the epsilon rules in an automaton.  Iterators may be
     * invalidated if the automaton is modified.
     */
    typedef std::vector<erule_t>::const_iterator erule_iterator;
    /** 
     * Type of constant bidirectional iterator that is used to iterate 
     * through the rules in an automaton.  Iterators may be invalidated if
     * the automaton is modified.
     */
    typedef std::vector<rule_t>::const_iterator rule_iterator;
    /** 
     * Constructs a tree automaton over the theory with no states, every
     * predicate accepting no models, and no epsilon or regular rules.
     */
    ta_t(const theory_t& theory);
  private:
    friend const theory_t& theory(const ta_t& ta);
    friend bool member(const ta_t& theory, const state_t& state);
    friend const state_iterator states_begin(const ta_t& ta);
    friend const state_iterator states_end(const ta_t& ta);
    friend const state_iterator add_state(ta_t& ta, const state_t& state);
    friend const state_predicate_t&
            predicate(const ta_t& ta, const kind_t& kind);
    friend void set_predicate(ta_t& ta, const state_predicate_t& pred);
    friend const erule_iterator erules_begin(const ta_t& ta);
    friend const erule_iterator erules_end(const ta_t& ta);
    friend void add_erule(ta_t& ta, const erule_t& erule);
    friend const rule_iterator rules_begin(const ta_t& ta);
    friend const rule_iterator rules_end(const ta_t& ta);
    friend void add_rule(ta_t& ta, const rule_t& rule);
    /** Pointer to implementation. */
    boost::shared_ptr<ta_impl> impl_;
  };
  /**
   * Returns theory of automaton.
   * \relates ta_t
   */
  const theory_t& theory(const ta_t& ta) CETA_DSO_EXPORT;
  /**
   * Returns true if state is in the automaton.
   * \relates ta_t
   */
  bool member(const ta_t& ta, const state_t& state) CETA_DSO_EXPORT;
  /**
   * Returns iterator that points to first state in the automaton.
   * \relates ta_t
   */
  const ta_t::state_iterator states_begin(const ta_t& ta) CETA_DSO_EXPORT;
  /**
   * Returns iterator that points one past the last state in the automaton.
   * \relates ta_t
   */
  const ta_t::state_iterator states_end(const ta_t& ta) CETA_DSO_EXPORT;
  /**
   * Adds state to automaton.
   * \relates ta_t
   */
  const ta_t::state_iterator
    add_state(ta_t& ta, const state_t& state) CETA_DSO_EXPORT;
  /** 
   * Returns acceptance predicate for the kind.
   * \relates ta_t
   */
  const state_predicate_t&
    predicate(const ta_t& ta, const kind_t& kind) CETA_DSO_EXPORT;
  /**
   * Sets particular predicate in tree automaton for kind of predicate.
   * \relates ta_t
   */
  void set_predicate(ta_t& ta,
                     const state_predicate_t& pred) CETA_DSO_EXPORT;
  /**
   * Returns iterator that points to first epsilon rule in the automaton.
   * \relates ta_t
   */
  const ta_t::erule_iterator erules_begin(const ta_t& ta) CETA_DSO_EXPORT;
  /**
   * Returns iterator that points one past the last epsilon rule in the 
   * automaton.
   * \relates ta_t
   */
  const ta_t::erule_iterator erules_end(const ta_t& ta) CETA_DSO_EXPORT;
  /**
   * Adds epsilon rule to the automaton.
   * \relates ta_t
   */
  void add_erule(ta_t& ta, const erule_t& erule) CETA_DSO_EXPORT;
  /**
   * Returns iterator that points to first rule in the automaton.
   * \relates ta_t
   */
  const ta_t::rule_iterator rules_begin(const ta_t& ta) CETA_DSO_EXPORT;
  /**
   * Returns iterator that points one past the last rule in the automaton.
   * \relates ta_t
   */
  const ta_t::rule_iterator rules_end(const ta_t& ta) CETA_DSO_EXPORT;
  /**
   * Adds rule to the automaton.
   * \relates ta_t
   */
  void add_rule(ta_t& ta, const rule_t& rule) CETA_DSO_EXPORT;
  /**
   * Writes tree automaton to string for debugging purposes.
   * \relates ta_t
   */
  std::ostream& operator<<(std::ostream& o, const ta_t& ta) CETA_DSO_EXPORT;
  /**
   * Checks if no term is accepted.
   * \relates ta_t
   */
  const test_result_t test_emptiness(const ta_t& ta) CETA_DSO_EXPORT;
  /**
   * Returns tree automata accepting complement of language accepted by ta.
   * \relates ta_t
   */
  const ta_t operator!(const ta_t& ta) CETA_DSO_EXPORT;
  /**
   * Modifies automaton so that language accepted is intersection of current
   * language and language accepted by rhs.
   * \relates ta_t
   */
  ta_t& operator&=(ta_t& lhs, const ta_t& rhs) CETA_DSO_EXPORT;
  /**
   * Modifies automaton so that language accepted is union of current
   * language and language accepted by rhs.
   * \relates ta_t
   */
  ta_t& operator|=(ta_t& lhs, const ta_t& rhs) CETA_DSO_EXPORT;
  /**
   * Returns automaton that accepts language accepted by both lhs and rhs
   * while renaming states if states in lhs and rhs overlap.
   * \relates ta_t
   */
  inline
  const ta_t operator&(const ta_t& lhs, const ta_t& rhs) {
    ta_t result = lhs;
    result &= rhs;
    return result;
  }
  /**
   * Returns automaton that accepts language accepted by lhs or rhs
   * while renaming states if states in lhs and rhs overlap.
   * \relates ta_t
   */
  inline
  const ta_t operator|(const ta_t& lhs, const ta_t& rhs) {
    ta_t result = lhs;
    result |= rhs;
    return result;
  }
}
#endif
