AUTOMAKE_OPTIONS = foreign

LDADD    = -lstdc++ -lgcc
AM_CPPFLAGS = -I$(top_srcdir)/ceta

AM_LDFLAGS  =

CETA_LIB = ceta/libceta.a

include $(top_srcdir)/ceta/rules.am
include $(top_srcdir)/examples/rules.am
include $(top_srcdir)/tests/rules.am

EXTRA_PROGRAMS = examples/example1
examples : $(EXTRA_PROGRAMS)

docdir = $(CETA_DOCDIR)
dist_doc_DATA = AUTHORS COPYING INSTALL README copyright
dist_noinst_DATA = doc/api_config doc/dev_config doc/main_page.dox
noinst_DATA = doc/api_stamp

doc/api_stamp : ceta/ceta.hh doc/main_page.dox doc/api_config
	if [ -x ${DOXYGEN} ] ; then \
		${DOXYGEN} doc/api_config ;\
	else echo "Doxygen not installed." ;\
	fi
	touch doc/api_stamp

documentation : doc/api_stamp

dev-documentation :
	if [ -x ${DOXYGEN} ] ; then \
		${DOXYGEN} doc/dev_config; \
	else echo "Doxygen not installed."; \
	fi


install-data-local : documentation
	test -z "$(CETA_DOCDIR)" || mkdir -p -- "$(CETA_DOCDIR)"
	test -d doc/api/html && cp -r doc/api/html $(CETA_DOCDIR)

mostlyclean-local :
	-rm -rf doc/api
	-rm -rf doc/dev
	-rm -rf doc/api_stamp
