if BUNDLED_ISL
    MAYBE_ISL = isl
    ISL_LA = $(top_builddir)/isl/libisl.la
endif

SUBDIRS = $(MAYBE_ISL) .
DIST_SUBDIRS = $(MAYBE_ISL)

FORCE:
isl/libisl.la: FORCE
	cd isl; $(MAKE) $(AM_MAKEFLAGS) libisl.la

ACLOCAL_AMFLAGS = -I m4

LIB_ISL = $(ISL_LA) @ISL_LIBS@

lib_LTLIBRARIES = libpet.la libpet_cxx.la
bin_PROGRAMS = @extra_bin_programs@
noinst_PROGRAMS = @extra_noinst_programs@ pet_codegen pet_check_code
EXTRA_PROGRAMS = pet pet_scop_cmp
TESTS = @extra_tests@
EXTRA_TESTS = pet_test.sh codegen_test.sh
TEST_EXTENSIONS = .sh

include_HEADERS = include/pet.h include/pet_cxx.h

EXTRA_DIST = \
	tests

PET_INCLUDES = -I$(srcdir) -I$(srcdir)/include

AM_CFLAGS = $(PET_INCLUDES) @ISL_CFLAGS@
AM_CXXFLAGS = $(PET_INCLUDES) $(CLANG_CXXFLAGS) @ISL_CFLAGS@ -pthread
AM_LDFLAGS = $(CLANG_LDFLAGS)

libpet_la_SOURCES = \
	isl_type_information.cc \
	aff.h \
	aff.c \
	array.h \
	array.c \
	clang.h \
	clang.cc \
	context.h \
	context.c \
	expr.h \
	expr.c \
	expr_access_type.h \
	expr_arg.h \
	expr_arg.c \
	filter.h \
	filter.c \
	loc.h \
	loc.c \
	nest.h \
	nest.c \
	options.h \
	options.c \
	print.c \
	print.h \
	tree.h \
	tree.c \
	tree2scop.h \
	tree2scop.c \
	scan.h \
	scan.cc \
	scop.h \
	scop.c \
	scop_plus.h \
	scop_plus.cc \
	skip.h \
	skip.c \
	state.h \
	summary.h \
	summary.c \
	value_bounds.h \
	value_bounds.c \
	version.h \
	version.cc \
	initialize_pet.c \
	pet.cc
libpet_la_LDFLAGS = -version-info @versioninfo@ $(AM_LDFLAGS)
libpet_la_LIBADD =  -lclangParse -lclangSema -lclangFrontend -lclangDriver\
	$(LIB_CLANG_EDIT) -lclangAnalysis \
	-lclangAST -lclangLex -lclangBasic -lclangSerialization \
	$(CLANG_LIBS) $(CLANG_LDFLAGS) $(LIB_ISL) -ldl -lz -lcursesw

libpet_cxx_la_SOURCES = \
	isl_type_information.cc \
	aff.h \
	aff.c \
	array.h \
	array.c \
	clang.h \
	clang.cc \
	context.h \
	context.c \
	expr.h \
	expr.c \
	expr_access_type.h \
	expr_arg.h \
	expr_arg.c \
	filter.h \
	filter.c \
	loc.h \
	loc.c \
	nest.h \
	nest.c \
	options.h \
	options.c \
	print.c \
	print.h \
	tree.h \
	tree.c \
	tree2scop.h \
	tree2scop.c \
	scan.h \
	scan.cc \
	scop.h \
	scop.c \
	scop_plus.h \
	scop_plus.cc \
	skip.h \
	skip.c \
	state.h \
	summary.h \
	summary.c \
	value_bounds.h \
	value_bounds.c \
	version.h \
	version.cc \
	initialize_pet.c \
	pet_cxx.cc
libpet_cxx_la_LDFLAGS = -version-info @versioninfo@ $(AM_LDFLAGS)
libpet_cxx_la_LIBADD =  -lclangParse -lclangSema\
	$(LIB_CLANG_EDIT) -lclangAnalysis \
	-lclangAST -lclangLex -lclangBasic -lclangSerialization \
	$(CLANG_LIBS) $(CLANG_LDFLAGS) $(LIB_ISL)

pet_CFLAGS = $(AM_CFLAGS) @LIBYAML_CPPFLAGS@
pet_LDFLAGS = $(AM_LDFLAGS) @LIBYAML_LDFLAGS@
pet_SOURCES = \
	dummy.cc \
	emit.c \
	scop_yaml.h \
	main.c
pet_LDADD = libpet.la $(LIB_ISL) -lyaml

pet_scop_cmp_CFLAGS = $(AM_CFLAGS) @LIBYAML_CPPFLAGS@
pet_scop_cmp_LDFLAGS = @LIBYAML_LDFLAGS@
pet_scop_cmp_LDADD = libpet.la $(LIB_ISL) -lyaml
pet_scop_cmp_SOURCES = \
	dummy.cc \
	scop_yaml.h \
	parse.c \
	pet_scop_cmp.c

pet_codegen_CFLAGS = $(AM_CFLAGS)
pet_codegen_LDFLAGS =
pet_codegen_LDADD = libpet.la $(LIB_ISL)
pet_codegen_SOURCES = \
	dummy.cc \
	pet_codegen.c

pet_check_code_CFLAGS = $(AM_CFLAGS)
pet_check_code_LDFLAGS =
pet_check_code_LDADD = libpet.la $(LIB_ISL)
pet_check_code_SOURCES = \
	dummy.cc \
	pet_check_code.c

dist-hook:
	echo @GIT_HEAD_VERSION@ > $(distdir)/GIT_HEAD_ID

gitversion.h: @GIT_HEAD@
	$(AM_V_GEN)echo '#define GIT_HEAD_ID "'@GIT_HEAD_VERSION@'"' > $@

install-data-local:
	@test -z "$(DESTDIR)$(libdir)/pet" || $(mkdir_p) "$(DESTDIR)$(libdir)/pet"
	$(INSTALL_DATA) "$(top_srcdir)/cmake/pet-config.cmake" "$(DESTDIR)$(libdir)/pet/"
	
uninstall-local:
	rm -f "$(DESTDIR)$(libdir)/pet/pet-config.cmake"



total:
	@echo "             /*-----------------------------------------------*"
	@echo "              *                     pet                       *"
	@echo "              *-----------------------------------------------*/"
	$(MAKE) uninstall
	$(MAKE) clean
	$(MAKE)
	$(MAKE) install
