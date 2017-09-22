/* Copyright 2006 University of Illinois at Urbana-Champaign
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
#ifndef _assoc_explorer_hh_
#define _assoc_explorer_hh_

#include "closure.hh"
#include "learncfg.hh"
#include "op_explorer.hh"
#include "reachable_image.hh"

namespace ceta {
  /** Reachable set explorer for an associative operator. */
  class assoc_explorer_t : public op_explorer_t {
  public:
    assoc_explorer_t(const theory_t& theory,
                     const op_t& op,
                     const closure_t& closure,
                     const std::vector<rule_t>& rules)
      : theory_(theory),
        op_(op),
        axioms_(axioms(theory, op)),
        image_(lhs_states(rules.begin(), rules.end())),
        explorer_(make_rules<cfg::chomsky_rules_t<state_t> >(closure, op)) {
    }

    /** Add reachable term and set to explorer. */
    void add_reachable(const std::set<state_t>& set, const term_t& term) {
      if ((kind(term) == output(op_))
              && (root(term) != op_)
              && !is_identity(root(term), axioms_)) {
        bool added = image_.add(set, term);
        if (added) {
          const std::set<state_t>& nset = back(image_).first;
          size_t last_index = state_count(image_) - 1;
          explorer_.add_terminal(last_index, nset.begin(), nset.end());
        }
      }
    }

    void explore(reachable_sets_t& reachables) {
      // Maximum number of times to call work when exploring.
      const size_t max_work_count = 40;
      size_t i = 0;
      while (!explorer_.complete()
          && !explorer_.has_reachable()
          && (i < max_work_count)) {
        explorer_.work();
        ++i;
      }
      while (explorer_.has_reachable()) {
        const std::set<state_t>& states = explorer_.reachable();
        if (!reachables.contains(states, op_)) {
          const std::vector<size_t>& next_string = explorer_.string();
          std::vector<term_t> subterms;
          subterms.reserve(next_string.size());
          // Build term from string.
          typedef std::vector<size_t>::const_iterator iter;
          for (iter i = next_string.begin(); i != next_string.end(); ++i) {
            const term_t& term = (image_.begin() + *i)->second;
            subterms.push_back(term);
          }
          term_t term(theory_, op_, subterms.begin(), subterms.end());
          reachables.add(states, term);
        }
        explorer_.pop_reachable();
      }
    }

    /** Returns true if this explorer has completely explored states. */
    virtual bool is_complete(void) const {
      return explorer_.complete();
    }
  private:
    /** Theory for explorer. */
    const theory_t theory_;
    /** Operator for explorer. */
    const op_t op_;
    /** Axioms for operator. */
    const axiom_set_t axioms_;
    /** Reachable states that are terminals in the explorer. */
    reachable_image_t image_;
    /** Underlying CFG explorer. */
    cfg::cfg_explorer_t<size_t, state_t> explorer_;
  };
}

#endif
