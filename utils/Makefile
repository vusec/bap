# Work around buggy Debian ocaml patch
# See http://bugs.debian.org/cgi-bin/bugreport.cgi?bug=678577
export OCAML_COMPAT='c'

export BAP_DIR=$(CURDIR)/..

# Don't send request to build Makefile to OCamlMakefile!
.PHONY: ../../utils-proj/Makefile
-include ../../utils-proj/Makefile

export USE_CAMLP4 = yes

export BAP_OCAMLDIR=$(BAP_DIR)/ocaml
export LIBTRACE=$(BAP_DIR)/libtracewrap/libtrace/src/ocaml

export OCAMLMAKEFILE=$(BAP_OCAMLDIR)/OCamlMakefile

include $(BAP_OCAMLDIR)/makefile.inc
ifdef HAVE_LLVM
export CODEGEN = codegen
export LLVM_PACKS = llvm llvm.analysis llvm.executionengine llvm.target llvm.scalar_opts llvm.bitwriter
endif

# Stop annoying warnings about big_int duplication!
#export OCAMLFIND_IGNORE_DUPS_IN=$(BAP_DIR)/bigint-3.12/otherlibs/num

# ocamlfind packages required
export PACKS = bigarray str num unix camomile piqi.lib piqi.runtime zarith batteries objsize oUnit ocamlgraph pcre $(LLVM_PACKS)
export LIBS = libtrace bap
export INCDIRS = $(BAP_OCAMLDIR) $(LIBTRACE) $(LIBTRACE)/piqi

# -rdynamic lets LLVM JIT see dynamic symbols
export LDFLAGS = -rdynamic

# Include sources from ../ocaml in the automatically generated dependencies.
export SOURCE_DIRS_IN = $(BAP_OCAMLDIR) $(BAP_PROJ_OCAMLDIR)

# When BAP lib changes, we need to recompile utilities
export RESULTDEPS = $(BAP_OCAMLDIR)/bap.a

# default subprojects to build
ifndef SUBPROJS
	export SUBPROJS = $(PROJUTILS) $(CODEGEN) toil iltrans ileval topredicate formula get_functions split streamtrans backtaint
endif

define PROJ_toil
	RESULT=toil
	SOURCES = toil.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_toil

define PROJ_iltrans
	RESULT=iltrans
	SOURCES = iltrans.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_iltrans

define PROJ_ileval
	RESULT=ileval
	SOURCES = ileval.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_ileval

define PROJ_topredicate
	RESULT=topredicate
	SOURCES = topredicate.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_topredicate

define PROJ_formula
	RESULT=formula
	SOURCES = formula.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_formula

define PROJ_get_functions
	RESULT=get_functions
	SOURCES = get_functions.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_get_functions

define PROJ_split
	RESULT=split_disjunction
	SOURCES = split_disjunction.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_split

define PROJ_streamtrans
	RESULT=streamtrans
	SOURCES = streamtrans.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_streamtrans

define PROJ_codegen
	RESULT=codegen
	SOURCES = codegen.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_codegen

define PROJ_backtaint
	RESULT=backtaint
	SOURCES = backtaint.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_backtaint

# suffix for bytecode (which when we make all is debug code)
export BCSUFFIX = .dbg

all: nc dc

# Recursive make
tags:
	echo 'Making tags (not really)'

# Print out command line to start ocamldebug
debug: dc
	@echo ocamldebug -I $(BIGINT) -I $(BAP_OCAMLDIR) -I $(BATT) -I $(OUNIT) -I $(PCRE) -I $(OBJSIZE) program

%:
	make -f $(OCAMLMAKEFILE) subprojs SUBTARGET=$@


# You may also tell "make" at the command-line what kind of target to
# produce (e.g. "make nc").  Here all the possibilities with shortcuts
# between parenthesis:
# 
#    * byte-code                     (bc)
#    * byte-code-nolink              (bcnl)   - no linking stage
#    * byte-code-library             (bcl)
#    * native-code                   (nc)
#    * native-code-nolink            (ncnl)   - no linking stage
#    * native-code-library           (ncl)
#    * debug-code                    (dc)
#    * debug-code-nolink             (dcnl)   - no linking stage
#    * debug-code-library            (dcl)
#    * profiling-byte-code           (pbc)
#    * profiling-byte-code-library   (pbcl)
#    * profiling-native-code         (pnc)
#    * profiling-native-code-library (pncl)
#    * byte-code-dll                 (bcd)
#    * native-code-dll               (ncd)
#    * pack-byte-code              (pabc)
#    * pack-native-code            (panc)
#    * toplevel interpreter          (top)
#    * subprjs
