AUTOMAKE_OPTIONS = foreign

if HAVE_DOT
  HAVE_DOT = YES
else
  HAVE_DOT = NO
endif

if HAVE_DOXYGEN
if BUILD_DEV_DOC
  DOXYGEN_CONFIG = dev_config
  DOXYGEN_DEPENDS = $(DIST_SOURCES)
  DOXYGEN_INPUTS = "$(srcdir)/ceta $(srcdir)/tests"
else
  DOXYGEN_CONFIG = api_config
  DOXYGEN_DEPENDS = $(pkginclude_HEADERS)
  DOXYGEN_INPUTS = "$(srcdir)/ceta/export.h \
		    $(srcdir)/ceta/ta.hh \
		    $(srcdir)/ceta/subset_construction.hh \
		    $(srcdir)/ceta/ceta.hh"
endif
DOXYGEN_DIR = api
api : doc/$(DOXYGEN_CONFIG) doc/main_page.dox $(DOXYGEN_DEPENDS)
	cp $(srcdir)/doc/$(DOXYGEN_CONFIG) doxygen.cfg
	echo "PROJECT_NAME = $(PACKAGE)" >> doxygen.cfg
	echo "PROJECT_NUMBER = $(VERSION)" >> doxygen.cfg
	echo "INPUT = $(srcdir)/doc/main_page.dox $(DOXYGEN_INPUTS)" \
	  >> doxygen.cfg
	echo "EXAMPLE_PATH = $(srcdir)/examples" >> doxygen.cfg
	echo "OUTPUT_DIRECTORY = api" >> doxygen.cfg
	echo "HTML_OUTPUT = ." >> doxygen.cfg
	echo "HAVE_DOT = $(HAVE_DOT)" >> doxygen.cfg
	echo "DOT_PATH = $(DOT)" >> doxygen.cfg
	$(DOXYGEN) doxygen.cfg

install-doxygen-html : api
	test -z "$(DESTDIR)$(htmldir)/api" \
	  || $(mkdir_p) "$(DESTDIR)$(htmldir)/api"
	for f in `(find api -type f)`; do             \
  	    $(INSTALL_DATA) $$f $(DESTDIR)$(htmldir)/$$f; \
  	done

uninstall-doxygen-html :
	rm -rf "$(DESTDIR)$(htmldir)/api"

clean-doxygen-html :
	-rm -rf api

html-local : api

INSTALL_DOXYGEN = install-doxygen-html
UNINSTALL_DOXYGEN = uninstall-doxygen-html
CLEAN_DOXYGEN = clean-doxygen-html
.PHONY : install-doxygen-html uninstall-doxygen-html clean-doxygen-html
else
DOXYGEN_DIR =
INSTALL_DOXYGEN =
UNINSTALL_DOXYGEN =
CLEAN_DOXYGEN =
endif

LDADD    = -lstdc++ -lgcc
AM_CPPFLAGS = -I$(top_srcdir)/ceta
AM_LDFLAGS  =

CETA_SO_LIB = libceta.so.1
CLEANFILES = doxygen.cfg ceta/$(CETA_SO_LIB)

CETA_LIB = -lceta
TESTS_ENVIRONMENT = LD_LIBRARY_PATH=ceta

lib_LIBRARIES = ceta/libceta.a

pkginclude_HEADERS = ceta/export.h \
                     ceta/ta.hh \
                     ceta/subset_construction.hh \
		     ceta/membership.hh \
                     ceta/ceta.hh

ceta_libceta_a_SOURCES = ceta/ac_parser.hh \
                         ceta/assoc_explorer.hh \
                         ceta/bi_graph.hh \
                         ceta/ceta.hh \
                         ceta/cfg.hh \
                         ceta/closure.hh \
                         ceta/closure.cc \
                         ceta/comm_explorer.hh \
                         ceta/counter_ac_explorer.hh \
                         ceta/counter_ac_explorer.cc \
                         ceta/earley.hh \
			 ceta/export.h \
                         ceta/free_explorer.hh \
                         ceta/lcounter_ac_explorer.hh \
                         ceta/lcounter_ac_explorer.cc \
                         ceta/ldsolver.hh \
                         ceta/ldsolver.cc \
                         ceta/learn.hh \
                         ceta/learncfg.hh \
                         ceta/matrix.hh \
			 ceta/membership.hh \
			 ceta/membership.cc \
                         ceta/op_explorer.hh \
                         ceta/parikh.hh \
                         ceta/qcontainer.hh \
                         ceta/reachable_image.hh \
                         ceta/reachable_sets.hh \
                         ceta/semilinear_ac_explorer.hh \
                         ceta/semilinear_ac_explorer.cc \
                         ceta/sls.hh \
                         ceta/sls.cc \
                         ceta/subset_construction.hh \
                         ceta/subset_construction.cc \
                         ceta/ta.hh \
                         ceta/ta.cc \
			 ceta/trans_closure.hh \
                         ceta/writer.hh

ceta/$(CETA_SO_LIB) : $(ceta_libceta_a_OBJECTS)
	$(CXXLINK) -shared -Wl,-soname,$(CETA_SO_LIB) \
		   $(ceta_libceta_a_OBJECTS)
	chmod a-x ceta/$(CETA_SO_LIB)

examples_example1_SOURCES = examples/example1.cc
examples_example1_LDADD = $(LDADD) $(CETA_LIB)

examples_example2_SOURCES = examples/example2.cc
examples_example2_LDADD = $(LDADD) $(CETA_LIB)

examples_tester_SOURCES = examples/tester.cc
examples_tester_LDADD = $(LDADD) $(CETA_LIB)

EXTRA_PROGRAMS = examples/example1 examples/example2 examples/tester
examples : $(EXTRA_PROGRAMS)

TESTS = tests/testmatrix \
        tests/testld \
        tests/testsls \
        tests/testparikh \
        tests/testearley \
        tests/testlearncfg \
        tests/testacparser \
        tests/testclosure \
	tests/testmembership \
        tests/testceta

check_PROGRAMS = $(TESTS)

tests_testmatrix_SOURCES   = tests/testmatrix.cc

tests_testld_SOURCES       = tests/testld.cc \
			     ceta/ldsolver.cc ceta/ldsolver.hh

tests_testsls_SOURCES      = tests/testsls.cc \
			     ceta/ldsolver.cc ceta/ldsolver.hh \
			     ceta/sls.cc ceta/sls.hh

tests_testparikh_SOURCES   = tests/testparikh.cc \
			     ceta/ldsolver.cc ceta/ldsolver.hh \
			     ceta/sls.cc ceta/sls.hh \
			     ceta/parikh.hh

tests_testearley_SOURCES   = tests/testearley.cc \
                             ceta/earley.hh ceta/qcontainer.hh

tests_testlearncfg_SOURCES = tests/testlearncfg.cc \
                             ceta/learncfg.hh \
                             ceta/learn.hh \
                             ceta/earley.hh ceta/qcontainer.hh

tests_testacparser_SOURCES = tests/testacparser.cc \
			     ceta/ldsolver.cc ceta/ldsolver.hh \
                             ceta/ac_parser.hh

tests_testclosure_SOURCES  = tests/testclosure.cc \
			     ceta/closure.cc ceta/closure.hh \
			     ceta/ta.cc ceta/ta.hh

tests_testmembership_SOURCES = tests/testmembership.cc
tests_testmembership_LDADD   = $(LDADD) -Lceta $(CETA_LIB)

tests_testceta_SOURCES     = tests/testceta.cc
tests_testceta_LDADD       = $(LDADD) -Lceta $(CETA_LIB)


dist_doc_DATA = AUTHORS COPYING INSTALL README copyright
dist_noinst_DATA = doc/api_config doc/dev_config doc/main_page.dox

# Install shared library

install-exec-local :
	$(INSTALL_DATA) ceta/$(CETA_SO_LIB) $(DESTDIR)$(libdir)/$(CETA_SO_LIB)
	ln -fs $(DESTDIR)$(libdir)/$(CETA_SO_LIB) \
	       $(DESTDIR)$(libdir)/libceta.so
install-data-local : $(INSTALL_DOXYGEN)

nodist_noinst_DATA = ceta/$(CETA_SO_LIB) $(DOXYGEN_DIR)

mostlyclean-local : $(CLEAN_DOXYGEN)

uninstall-local : $(UNINSTALL_DOXYGEN)
	rm -f "$(DESTDIR)$(libdir)/$(CETA_SO_LIB)"
	rm -f "$(DESTDIR)$(libdir)/libceta.so"

