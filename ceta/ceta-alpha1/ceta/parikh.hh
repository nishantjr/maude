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
#ifndef _parikh_hh_
#define _parikh_hh_
/** \file
 * A datastructure for context free grammars and algorithm for computing
 * its Parikh image.
 */

#include <map>
#include <ostream>

#include "export.h"
#include "proxy.hh"


namespace ceta {
  class semilinear_set;

/** Namespace for context free grammar and related classes. */
namespace cfg {
  class symbol_impl;

  /** Indicator of whether a symbol is terminal or non-terminal. */
  enum symbol_type_t {terminal, nonterminal};

  /**
   * A terminal or non-terminal symbol in a context-free grammar.  A symbol
   * is a lightweight object associated to a non-unique identifier.  Its
   * lifetime is dependent on the context free grammar that it is part of.
   * \sa cfg_t::add_terminal
   * \sa cfg_t::add_nonterminal
   */
  class symbol_t 
    : public comparable_view_proxy<const symbol_impl, symbol_t> {
  public:
    /** Constructs an unitialized symbol. */
    symbol_t(void) {
    }

    /**
     * \internal
     * Constructs a symbol given a pointer to its internal representation.
     */
    symbol_t(const symbol_impl* impl)
      : comparable_view_proxy<const symbol_impl, symbol_t>(impl) {
    }

    /** Returns the type of this symbol. */
    symbol_type_t type(void) const;
    /** Returns the identifier of this symbol. */
    std::string id(void) const;
    /** Returns an integer index identifying this symbol. */
    size_t index(void) const;
  };

  /**
   * Writes the symbol's identifier to the output stream.
   * \relates symbol_t
   */
  inline
  std::ostream& operator<<(std::ostream& o, const symbol_t& s) {
    return o << s.id();
  }
  
  struct cfg_impl;
  
  /**
   * Mapping from symbols to the semilinear set corresponding to the
   * Parikh image of strings reaching that symbol.
   */
  typedef std::map<symbol_t, semilinear_set> parikh_map_t;

  /** A context free grammar. */
  class cfg_t {
  public:
    /** Constructs a new empty context free grammar. */
    cfg_t(void);
    ~cfg_t(void);
  
    /** Adds a new terminal symbol with the provided identifer. */
    symbol_t add_terminal(const char* id);
    /** Adds a new non-terminal symbol with the provided identifer. */
    symbol_t add_nonterminal(const char* id);

    /// Adds a transition lhs -> rhs to this grammar.
    void add_transition(symbol_t lhs, symbol_t rhs) {
      add_transition(&lhs, &lhs + 1, rhs);
    }

    /// Adds a transition [lhs_begin ... lhs_end) -> rhs to this grammar.
    void add_transition(const symbol_t* lhs_begin, const symbol_t* lhs_end,
                        symbol_t rhs);
  
    
    /**
     * Computes the parikh image of every non-terminal symbol in the grammar.
     */
    parikh_map_t parikh_image(void) const;
  private:
    // Disallow copy construction and assignment
    cfg_t(const cfg_t&);
    cfg_t& operator=(const cfg_t&);

    cfg_impl* impl_;
  };
}
}

#endif
