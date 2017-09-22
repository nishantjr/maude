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
#ifndef _proxy_hh_
#define _proxy_hh_
/** \file
 * Proxy classes which can aid in hiding a class's implementation.
 */

#include "export.h"

namespace ceta {
  /** 
   * A templated read-only proxy for encapsulating a pointer to an
   * implementation.  The proxy does not require that its template argument
   * <code>T</code> be defined, and so it can be used to hide a class
   * declaration from view.  In order to allow proxies to be used in STL
   * collections, proxies are comparable by using the address of the object
   * they point to.
   */
  template<typename T, typename Derived>
  class comparable_view_proxy {
  public:
    /** Returns true if this instancce has been properly initialized. */
    bool is_assigned(void) const {
      return impl_ != NULL;
    }

    /** Returns a reference to implementation. */
    T& operator*(void) {
      return *impl_;
    }

    /** Returns a const reference to implementation. */
    const T& operator*(void) const {
      return *impl_;
    }

    /** Returns a pointer to implementation. */
    T* operator->(void) {
      return impl_;
    }

    /** Returns a const pointer to implementation. */
    const T* operator->(void) const {
      return impl_;
    }

    /** Returns true if instances point to same location. */
    bool operator==(const Derived& o) const {
      return impl_ == o.impl_;
    }

    template<class U>
    bool operator==(const U& o) const {
      return impl_ == o.impl_;
    }

    /** Returns true if instances do not point to same location. */
    bool operator!=(const Derived& o) const {
      return impl_ != o.impl_;
    }

    /** 
     * Returns true if location this instance points to less than location
     * other instance points to.
     */
    bool operator<(const Derived& o) const {
      return impl_ < o.impl_;
    }

    /** 
     * Returns true if location this instance points to less than or equal
     * to location other instance points to.
     */
    bool operator<=(const Derived& o) const {
      return impl_ <= o.impl_;
    }

    /** 
     * Returns true if location this instance points to greater than location
     * other instance points to.
     */
    bool operator>(const Derived& o) const {
      return impl_ > o.impl_;
    }

    /** 
     * Returns true if location this instance points to greater than or
     * equal to location other instance points to.
     */
    bool operator>=(const Derived& o) const {
      return impl_ >= o.impl_;
    }

  protected:
    /** Constructs a proxy with a <code>NULL</code> implementation. */
    comparable_view_proxy(void)
      : impl_(NULL) {
    }

    /** Constructs a proxy for the provided implementation. */
    comparable_view_proxy(T* impl)
      : impl_(impl) {
    }

    /** Destructs a proxy. */
    ~comparable_view_proxy() {
    }

    /** Pointer to implementation this is a proxy for. */
    T* impl_;
  };

  template<typename T>
  class owner_proxy_t {
  public:
    owner_proxy_t(const owner_proxy_t& o)
      : impl_(o.impl_),
        count_(o.count_) {
      if (count_ != NULL)
        ++(*count_);
    }

    owner_proxy_t& operator=(const owner_proxy_t& o) {
      if (impl_ != o.impl_) {
        release();
        impl_ = o.impl_;
        count_ = o.count_;
        if (count_ != NULL)
          ++(*count_);
      }
      return *this;
    }
    
    ~owner_proxy_t(void) {
      release();
    }
  protected:
    owner_proxy_t(void)
      : impl_(NULL),
        count_(NULL) {
    }

    bool is_assigned(void) const {
      return impl_ != NULL;
    }

    /** Sets impl_ to null and frees it if count reaches 0. */
    void release(void) {
      if (impl_ != NULL) {
        --(*count_);
        if (*count_ == 0) {
          delete_impl(impl_);
          delete count_;
          impl_ = NULL;
          count_ = NULL;
        }
      }
    }

    void set(T* new_impl) {
      if (impl_ == new_impl) return;
      if (new_impl == NULL) {
        release();
      } else {
        size_t* new_count = new size_t;
        release();
        impl_ = new_impl;
        count_ = new_count;
        *(count_) = 1;
      }
    }
  
    /** Returns a reference to implementation that callers may modify. */
    T& modifiable_impl(void) {
      if (*count_ != 1) {
        size_t* new_count_ = new size_t;
        try {
          impl_ = new T(*impl_);
          --(*count_);
          count_ = new_count_;
          *count_ = 1;
        } catch (...) {
          delete new_count_;
          throw;
        }
      }
      return *impl_;
    }

    /** Returns a const reference to implementation. */
    const T& impl(void) const {
      return *impl_;
    }

  private:
    /** Pointer to implementation. */
    T* impl_;
    /** Pointer to reference count for implementation. */
    size_t* count_;
  };
};
#endif
