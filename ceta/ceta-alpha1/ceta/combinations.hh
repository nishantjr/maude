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
#ifndef _combinations_hh_
#define _combinations_hh_

#include <cstddef>

namespace std {
  template<typename T>
  class iterator_traits;
}

/** 
 * Evaluates the unary functions pointed to by iterators in range [fn_begin
 * fn_end) on all possible values to compute closure of values with respect
 * to those functions.  FI is forward iterator that points to a "function".
 * The function should have a method explore that takes an element of values
 * and the list of values.  The function should add any new reachables 
 * directly to the list.  The list should have a member type named "iterator"
 * to indicate the type of its iterators and methods "begin" and "end" that 
 * return an iterator to the first element in values and one past the last
 * element in values respectively.
 */
template<typename FI, typename L>
void combinations(FI fn_begin, FI fn_end, L& values) {
  typedef typename L::iterator list_iter;
  // Iterator that points to the last input explored during the previous 
  // iterations.
  list_iter prev_last_value = values.begin();
  // Main iteration loop
  while (prev_last_value != values.end()) {
    // Fix end of loop for this round
    list_iter end = values.end();
    for (FI ifn = fn_begin; ifn != fn_end; ++ifn)
      for (list_iter i = prev_last_value; i != end; ++i)
        ifn->explore(*i, values);
    prev_last_value = end;
  }
}

template<typename F, typename TI, typename LII, typename L>
void combinations(F& fn,
                  TI arg_begin, TI arg_end,
                  LII prev,
                  L& values,
                  bool& found_new) {
  size_t arg_count = std::distance(arg_begin, arg_end);
  typedef typename std::iterator_traits<LII>::value_type LI;

  // Stores maximum input for each argument
  LI last_inputs[arg_count];
  // Indicates if there are any new inputs
  bool has_new_inputs = false;
  // Last entry in last_inputs with new inputs
  LI* last_new_input;

  // Initialize last_inputs, has_new_inputs, and last_new_input.
  {
    LI* cur_last = last_inputs;
    LII cur_prev = prev;
    for (TI i = arg_begin; i != arg_end; ++i) {
      *cur_last = values.end(*i);
      if (*cur_last != *cur_prev) {
        has_new_inputs = true;
        last_new_input = cur_last;
      }
      ++cur_prev;
      ++cur_last;
    }
  }


  // If there are no new inputs, skip
  if (has_new_inputs == false) return;

  // Stores number of iterators in inputs that point to a new argument
  size_t new_assigned_count(0);

  // Array for storing current input in loop
  LI inputs[arg_count];
  // Stores position of last input in inputs
  LI* inputs_end = inputs + arg_count;
  
  // If the last column with new inputs is the first column.
  if (last_inputs == last_new_input) {
    inputs[0] = *prev;
    ++new_assigned_count;
  } else {
    inputs[0] = values.begin(*arg_begin);
  }

  bool abort = false;

  // Stores current input
  LI* cur_input = inputs;
  LII cur_new = prev;
  LI* cur_last = last_inputs;
  TI cur_type = arg_begin;
  while (inputs[0] != last_inputs[0]) {
    // If we have reached maximum index for this argument
    if (*cur_input == *cur_last) {
      // We are no longer referencing a new_state, so decrement number of
      // columns referencing new arguments.
      --new_assigned_count;
      // Goto previous argument
      --cur_input;
      --cur_new;
      --cur_last;
      --cur_type;
      // Jump to next input.
      ++(*cur_input);
    // Else if we are still below last argument
    } else if (cur_input + 1 != inputs_end) {
      //  Goto next argument 
      ++cur_input; ++cur_new; ++cur_last; ++cur_type;
      // If we have not yet used a new argument and the next column is
      // the only column with new inputs
      if ((new_assigned_count == 0) && (cur_last == last_new_input)) {
        // Start next column at first input not yet reached
        *cur_input = *cur_new;
      } else {
        // Start next column at first input.
        *cur_input = values.begin(*cur_type);
      }
    // Else explore current state
    } else {
      fn.explore(inputs, values, found_new, abort);
      if (abort) return;
      // Goto next input
      ++(*cur_input);
    }
    // Increment new_assigned_count if we just reached first input not yet
    // explored.
    if (*cur_input == *cur_new) ++new_assigned_count;
  }

  // Update prev with inputs explored in this state
  std::copy(last_inputs, last_inputs + arg_count, prev);
}
#endif
