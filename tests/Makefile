.NOTPARALLEL:
# Work around buggy Debian ocaml patch
# See http://bugs.debian.org/cgi-bin/bugreport.cgi?bug=678577
export OCAML_COMPAT='c'

# XXX Fix this so it actually works
include C/Makefile.defs

export BAP_DIR=$(CURDIR)/..

.PHONY: $(BAP_DIR)/../tests-proj/Makefile
-include $(BAP_DIR)/../tests-proj/Makefile

export BAP_OCAMLDIR=$(BAP_DIR)/ocaml
export OCAMLMAKEFILE=$(BAP_OCAMLDIR)/OCamlMakefile
export LIBTRACE=$(BAP_DIR)/libtracewrap/libtrace/src/ocaml

# Stop annoying warnings about big_int duplication!
#export OCAMLFIND_IGNORE_DUPS_IN=$(BAP_DIR)/bigint-3.12/otherlibs/num

include $(BAP_OCAMLDIR)/makefile.inc
ifdef HAVE_LLVM
export LLVM_PACKS = llvm llvm.analysis llvm.executionengine llvm.target llvm.scalar_opts llvm.bitwriter
endif


export PACKS = bigarray str num unix camomile piqi.lib piqi.runtime zarith batteries oUnit pcre objsize ocamlgraph $(LLVM_PACKS)
export LIBS = libtrace bap
export INCDIRS= $(BAP_OCAMLDIR) $(LIBTRACE) $(LIBTRACE)/piqi

# Include sources from ../ocaml in the automatically generated dependencies.
export SOURCE_DIRS_IN = $(BAP_OCAMLDIR) $(BAP_PROJ_OCAMLDIR)

export SUBPROJS += $(PROJTESTS) baptest

CSRC=$(wildcard C/*.c)
CEXECS = $(CSRC:C/%.c=%)

# XXX Use ocamlmake to clean up asm executables?
TRASH = asm/nop C/test C/taint_test C/bof1

TARGETS = CTESTS ASM nc dc

define PROJ_baptest
	RESULT = bap_test_suite
	SOURCES = \
	il_suite.ml \
	var_suite.ml \
	ast_suite.ml \
	disasm_i386_suite.ml \
	asmir_suite.ml \
	eval_suite.ml \
	traces_suite.ml \
	predicate_suite.ml \
	arithmetic_suite.ml \
	dominator_suite.ml \
	bap_suite.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_baptest

export BCSUFFIX = .dbg

all: | $(TARGETS)

test: all
	./bap_test_suite

ASM:
	make -C asm

CTESTS:
	make -C C

.PHONY: tags
tags: TAGS

.PHONY: TAGS
TAGS:
	-otags $^

debug: dc
	@echo ocamldebug -I $(BIGINT) -I $(BAP_OCAMLDIR) -I $(BATT) -I $(OUNIT) -I $(PCRE) -I $(OBJSIZE) program

%:
	make -f $(OCAMLMAKEFILE) subprojs SUBTARGET=$@

