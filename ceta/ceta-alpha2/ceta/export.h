/**
 * \file 
 * Macros for exposing and hiding symbols in a shared library.
 */
#include <config.h>

#define NO_RETURN __attribute__((noreturn))

/** 
 * \def CETA_DSO_EXPORT
 * Declares the symbol should be visible outside the library.
 */
/**
 * \def CETA_DSO_LOCAL
 * Declares the symbol should only be internally visible.
 */
#ifdef HAVE_GCC_CLASS_VISIBILITY
  #define CETA_DSO_EXPORT  __attribute__((visibility ("default")))
  #define CETA_DSO_LOCAL   __attribute__((visibility ("internal")))
#else
  /** Exports the class2 */
  #define CETA_DSO_EXPORT
  #define CETA_DSO_LOCAL
#endif
