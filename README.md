## NOTES ON GIT BRANCHES FOR MAUDE + HOOKS

This branch contains the original Maude sources with the Termination Checker hooks used in Maude Formal Environment. It may be compiled in Linux and Mac OS X. This readme file includes all changes done on Maude source code.

### Initial repository setting

The original repository stands on https://github.com/maude-team/maude.git. Local copy for UMA is stored in //atenea02/gisum/uma/es/usr/jmalvarez/maude-githab/maude. Local repository is a clone of remote repository:

~~~
git clone https://github.com/maude-team/maude.git
~~~

A new branch has been created to host the MFE hooks (mfe-hooks):

~~~
cd maude
git branch mfe-hooks
git checkout mfe-hooks
~~~

Make has been built using the new verion of ncurses library installed in atenea02:

~~~
../configure CPPFLAGS="-I/usr/local/include -I/usr/local/include/ncurses" LDFLAGS="-static -L/usr/local/lib" GMP_LIBS="/usr/local/lib/libgmpxx.a /usr/local/lib/libgmp.a" LIBSIGSEGV_LIB="/usr/local/lib/libsigsegv.a" TECLA_LIBS="/usr/local/lib/libtecla.a /usr/local/lib/libncurses.a" BUDDY_LIB="/usr/local/lib/libbdd.a"
~~~

Maude source files are modified to incorporate the MFE hooks and new source code files are included in their corresponding directories:

~~~
./configure.ac

< AC_INIT(Maude, 2.6, [maude-bugs@maude.cs.uiuc.edu])
---
> AC_INIT(Maude-ceta, 2.6, [maude-bugs@maude.cs.uiuc.edu])
19c19
< AM_INIT_AUTOMAKE(Maude, 2.6)
---
> AM_INIT_AUTOMAKE(Maude-ceta, 2.6)

./src/BuiltIn/Makefile.am
37c37,38
<       equalityExtorFinal.cc
---
>       equalityExtorFinal.cc \
>       terminationCheckerSymbol.cc
64c65,66
<       equalityExtorFinal.hh
---
>       equalityExtorFinal.hh \
>       terminationCheckerSymbol.hh
~~~

Modified ./src/Mixfix/Makefile.am to include new headers in the libbuiltIn_a_CPPFLAGS list:

~~~
        -I$(top_srcdir)/src/Mixfix \
        -I$(top_srcdir)/src/IO_Stuff \
        -I$(top_srcdir)/src/Higher \
        -I$(top_srcdir)/src/StrategyLanguage \
        -I$(top_srcdir)/src/AU_Theory
~~~

Copied source files ./src/BuiltIn/terminationCheckerSymbol.hh and ./src/BuiltIn/terminationCheckerSymbol.cc
Made changes in ../src/Mixfix/entry.cc to include hook:

~~~
554a555,560
>     case SymbolType::TERMINATION_CHECKER_SYMBOL:
>        return new TerminationCheckerSymbol(name,nrArgs);
~~~

Made changes in ../src/Mixfix/mixfixModule.cc to include hook:

~~~
150a151,155
> // for ceta and termination checker
> #include "terminationCheckerSymbol.hh"
~~~

Made changes in ../src/Mixfix/specialSymbolTypes.cc to include hook:

~~~
56a57,59
>   MACRO(TerminationCheckerSymbol, SymbolType::TERMINATION_CHECKER_SYMBOL)
~~~

Made changes in ../src/Mixfix/symbolType.hh to include hook:

~~~
56a57,59
78a79,81
>     TERMINATION_CHECKER_SYMBOL,
~~~

Changed ./src/Mixfix/banner.cc to include a new line in the opening banner with information about the new features.

~~~
   s << "\t     With CETA and termination checker extensions \n";
~~~

Installation:

~~~
jmalvarez@atenea02:~/maude-github/maude$ autoconf
jmalvarez@atenea02:~/maude-github/maude$ automake
Useless use of /d modifier in transliteration operator at /usr/share/automake-1.9/Automake/Wrap.pm line 60.
configure.ac:19: version mismatch.  This is Automake 1.9.6,
configure.ac:19: but the definition used by this AM_INIT_AUTOMAKE
configure.ac:19: comes from Automake 1.11.3.  You should recreate
configure.ac:19: aclocal.m4 with aclocal and run automake again.
jmalvarez@atenea02:~/maude-github/maude$ aclocal
~~~

### Mac OS X Users

Maude + TerminationChecker hooks can be compiled on OS X, with a minor change:

In file `/src/BuiltIn/terminationCheckerSymbol.cc` added `#include <signal.h>`. 

## Adding scc hook

./src/configure.ac: Included test of presence of ceta lib.

~~~
125a126,133
> #
> #       Check if user set particular CETA libraries to use and if
> #       not set defaults.
> #
> if (test -z "$CETA_LIBS") then
>   CETA_LIBS="-lceta"
> fi
> AC_SUBST(CETA_LIBS)
~~

Modified ./src/Main/Makefile.am:

~~~
64a65
>       $(CETA_LIBS) \
86c87,89
<       metaInterpreter.maude
---
>       metaInterpreter.maude \
>       scc.maude \
>       scc2.maude
~~~

Modified ./src/Meta/Makefile.am:

~~~
19c19,20
<       -I$(top_srcdir)/src/StrategyLanguage
---
>       -I$(top_srcdir)/src/StrategyLanguage \
>       -I$(top_srcdir)/src/ACU_Theory
28c29,31
<       metaPreModule.cc
---
>       metaPreModule.cc \
>       cetaSymbol.cc \
>       completenessCheckerSymbol.cc
~~~ 

Copied new source files:

~~~
./src/Main: prelude-ceta.maude
./src/Main: scc2.maude
./src/Main: scc.maude

./src/Meta: cetaSymbol.cc
./src/Meta: cetaSymbol.hh
./src/Meta: completenessCheckerSymbol.cc
./src/Meta: completenessCheckerSymbol.hh
~~~

Modified changes in ../src/Mixfix/entry.cc to include hook:

~~~
554a555,560
>     case SymbolType::CETA_SYMBOL:
>        return new CetaSymbol(name, nrArgs);
>     case SymbolType::COMPLETENESS_CHECKER_SYMBOL:
>        return new CompletenessCheckerSymbol(name, nrArgs);
~~~

Made changes in ../src/Mixfix/mixfixModule.cc to include hook:

~~~
150a151,155
> // for ceta and termination checker
> #include "cetaSymbol.hh"
> #include "completenessCheckerSymbol.hh"

~~~

Made changes in ../src/Mixfix/specialSymbolTypes.cc to include hook:

~~~
56a57,59
>   MACRO(CetaSymbol, SymbolType::CETA_SYMBOL)
>   MACRO(CompletenessCheckerSymbol, SymbolType::COMPLETENESS_CHECKER_SYMBOL)

~~~

Made changes in ../src/Mixfix/symbolType.hh to include hook:

~~~
56a57,59
78a79,81
>     CETA_SYMBOL,
>     COMPLETENESS_CHECKER_SYMBOL,
~~~

Changed ./src/Mixfix/banner.cc to include a new line in the opening banner with information about the new features.

~~~
   s << "\t     With CETA and termination checker extensions \n";
~~~

Modified other source files.

./src/Meta/metaLevel.hh

~~~
197a198
>   DagNode* upOpDecl(ImportModule* m, Symbol* symbol, int declNr, PointerMap& qidMap);
270d270
<   DagNode* upOpDecl(ImportModule* m, int symbolNr, int declNr, PointerMap& qidMap);
~~~

./src/Meta/metaUpModule.cc

~~~
344a345
>       Symbol* symbol = m->getSymbols()[i];
347c348
<         args.append(upOpDecl(m, i, j, qidMap));
---
>         args.append(upOpDecl(m, symbol, j, qidMap));
511c512
< MetaLevel::upOpDecl(ImportModule* m, int symbolNr, int declNr, PointerMap& qidMap)
---
> MetaLevel::upOpDecl(ImportModule* m, Symbol* symbol, int declNr, PointerMap& qidMap)
515d515
<   Symbol* symbol = m->getSymbols()[symbolNr];
~~~

./src/Mixfix/banner.cc

~~~
57aO58
>   s << "\t     With CETA and termination checker extensions \n";
~~~
