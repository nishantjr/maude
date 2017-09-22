AC_INIT(ceta, alpha3a, jhendrix@uiuc.edu)
AC_LANG(C++)

dnl Init automake to not require GNU files (NEWS and Changelog), enable all
dnl warnings, and build object files in the appropriate subdirectory
AM_INIT_AUTOMAKE([foreign -Wall subdir-objects])
dnl Check CC supports -c and -o switches
AM_PROG_CC_C_O
dnl Do not rebuild generated files every time
AM_MAINTAINER_MODE

dnl Check for programs
CXXFLAGS="-Wall ${CXXFLAGS}"
AC_PROG_CXX
if (test "$GXX" = yes) then
  AC_MSG_CHECKING([g++ compiler version])
  GXX_VERSION=`$CXX -dumpversion`
  AC_MSG_RESULT($GXX_VERSION)
fi
AC_PROG_INSTALL
AC_PROG_RANLIB
AC_PROG_LN_S

dnl Check for Doxygen
AC_ARG_VAR([DOXYGEN], [Doxygen command])
AC_PATH_PROGS([DOXYGEN], [doxygen], [], [$PATH])

dnl Check for Boost
AC_CHECK_HEADERS(boost/shared_ptr.hpp,, AC_MSG_ERROR(Cannot find Boost))

dnl Check for C++ requirements
AC_C_CONST
AC_C_INLINE
AC_TYPE_SIZE_T
AC_CHECK_TYPES([ptrdiff_t])
AC_FUNC_ERROR_AT_LINE

#	If we are not debugging, assume we are optimizing.
#
AC_ARG_ENABLE(debug,
	      AC_HELP_STRING([--enable-debug],
                             [no optimization, dump routines [default=no]]),
	      [DEBUGGING=$enableval],
	      [DEBUGGING=no])

CETA_DOCDIR=\${prefix}/share/doc/${PACKAGE}
AC_ARG_WITH(docdir,
        AS_HELP_STRING([--with-docdir=DIR],
                [directory where documentation should be installed]),,)
AC_SUBST(CETA_DOCDIR)

if (test "$DEBUGGING" = no) then
  dnl Check for GCC class visibility attribute
  AC_MSG_CHECKING(for GCC class visibility attribute)
  CXXFLAGS_save="$CXXFLAGS"
  CXXFLAGS="$CXXFLAGS -Werror -fvisibility=internal"
  AC_COMPILE_IFELSE([
  class __attribute__ ((visibility ("hidden"))) c_hidden {
  };

  class __attribute__ ((visibility ("default"))) c_default {
  };

  int main (int argc, char **argv) {
    return 0;
  }
  ],have_gcc_class_visibility=yes,have_gcc_class_visibility=no)
  CXXFLAGS="$CXXFLAGS_save"
  AC_MSG_RESULT($have_gcc_class_visibility)
  if test "$have_gcc_class_visibility" = yes; then
    AC_DEFINE(HAVE_GCC_CLASS_VISIBILITY, 1,
              [Define to 1 if compiler supports visibility attributes])
    CXXFLAGS="-fvisibility=internal ${CXXFLAGS}"
  fi

  if test "$GXX" = yes; then
    OFLAGS="-O2 -fomit-frame-pointer -fforce-addr"
  else
    OFLAGS="-O"
  fi
  CXXFLAGS="$CXXFLAGS $OFLAGS"
fi

AC_CONFIG_HEADERS([config.h])
AC_CONFIG_FILES([Makefile])
AC_OUTPUT
