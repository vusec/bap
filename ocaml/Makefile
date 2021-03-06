# $Id: Makefile 6559 2012-07-30 01:23:22Z edmcman $

.NOTPARALLEL:
# Work around buggy Debian ocaml patch
# See http://bugs.debian.org/cgi-bin/bugreport.cgi?bug=678577
export OCAML_COMPAT='c'

export BAP_DIR=$(CURDIR)/..

export OCAMLMAKEFILE=OCamlMakefile
export LIBASMIR=../libasmir
export LIBTRACE=$(BAP_DIR)/libtracewrap/libtrace/src/ocaml

include $(LIBASMIR)/makefile.inc
export SOLVER=$(BAP_DIR)/solvers
include $(SOLVER)/makefile.inc
-include ../../ocaml-proj/Makefile

include $(CURDIR)/makefile.inc
ifdef HAVE_LLVM
export LLVM_SRC = llvm_codegen.mli llvm_codegen.ml
export LLVM_PACKS = llvm llvm.analysis llvm.executionengine llvm.target llvm.scalar_opts llvm.bitwriter
endif

#export LIB_PACK_NAME = bap

# common sources
export SOURCES = \
	debug.mli debug.ml \
	BatListFull.ml \
	util.mli util.ml \
	big_int_convenience.ml \
	dominator.ml \
	graphDataflow.mli graphDataflow.ml \
	type.mli type.ml \
	var.mli var.ml \
	arithmetic.ml \
	ast.ml \
	ssa.ml \
	disasm_temp.ml \
	pp.ml \
	typecheck.mli typecheck.ml \
	ast_convenience.ml \
	cfg.mli cfg.ml \
	ast_visitor.mli ast_visitor.ml \
	ssa_visitor.mli ssa_visitor.ml \
	grammar_scope.ml \
	memory2array.mli memory2array.ml \
	flatten_mem.mli flatten_mem.ml \
	reachable.mli reachable.ml \
	prune_unreachable.mli prune_unreachable.ml \
	cfg_pp.ml \
	cfg_ast.mli cfg_ast.ml \
	depgraphs.mli depgraphs.ml \
	cfg_ssa.mli cfg_ssa.ml \
	checks.mli checks.ml \
	debug_snippets.ml \
	sccvn.mli sccvn.ml \
	deadcode.mli deadcode.ml \
	ssa_simp_misc.ml \
	ssa_simp.ml \
	formulap.ml \
	stp.ml \
	smtlib1.ml \
	smtlib2.ml \
	libbfd.idl \
	libasmir.idl \
	disasm_i386.ml \
	disasm.ml \
	$(LLVM_SRC) \
	syscall_models.ml \
	gcl.mli gcl.ml \
	ugcl.ml \
	wp.mli wp.ml \
	stp_grammar.mly stp_lexer.mll \
	cvc3_grammar.mly cvc3_lexer.mll \
	yices_grammar.mly yices_lexer.mll \
	smtexec.mli smtexec.ml \
	solver.mli solver.ml \
	asmir_vars.ml \
	asmir_consts.ml \
	asmir.mli asmir.ml \
	asmir_rdisasm.mli asmir_rdisasm.ml \
	grammar_private_scope.ml \
	grammar.mly lexer.mll \
	parser.ml \
	input.mli input.ml \
	to_c.ml \
	vsa.ml \
	symbeval.ml symbeval_search.ml \
	ast_slice.ml \
	ssa_slice.ml \
	structural_analysis.ml \
	unroll.ml \
	hacks.ml \
	coalesce.mli coalesce.ml \
	traces.ml \
	traces_surgical.ml \
	traces_backtaint.mli traces_backtaint.ml \
	utils_common.ml \
	test_common.ml \
	template.ml \
	syscall_id.mli syscall_id.ml \
	graphDataflowW.ml \
	$(SOLVER_SOURCES) \
	$(PROJSOURCES) \

RESULT = bap
DOC_FILES := $(filter %.mli, $(SOURCES)) $(filter %.ml, $(SOURCES))

# ocamlfind packages required
export PACKS = bigarray str num unix camomile threads zarith batteries oUnit pcre objsize ocamlgraph $(LLVM_PACKS)
export DOCPACKS = $(PACKS)
export YFLAGS = -v

export USE_CAMLP4 = yes

export CLIBS = asmir vex opcodes bfd iberty stdc++
export CLIBS += $(SOLVER_CLIBS)
export CFLAGS = -g
export LDFLAGS = $(LIBASMIR_LDFLAGS) $(SOLVER_LDFLAGS)
export PPFLAGS = $(SOLVER_PPFLAGS) $(LLVM_PPFLAGS)
export INCDIRS = $(LIBTRACE) $(LIBTRACE)/piqi
export LIBS = libtrace
export RESULTDEPS = $(LIBASMIR)/src/libasmir.a $(VEX_DIR)/libvex.a $(LIBTRACE)/libtrace.cmxa
export LIBDIRS = $(LIBASMIR)/src $(VEX_DIR)
export LIBDIRS += $(SOLVER_LIBDIRS) $(LIBTRACE)

OCAMLLDFLAGS = -thread # just for make top
OCAMLFLAGS = -thread -warn-error Aelz -annot # -for-pack Bap #-w A
# merge everything but descriptions.
OCAMLDOCFLAGS = -m avlsoper

all: dcl ncl

bap_lib_doc: all htdoc

docall: all htdoc ladoc psdoc pdfdoc

tags: TAGS

TAGS: $(SOURCES)
	-otags $^

runtop:	top
	./bap.top -I $(BIGINT) -I $(BATT)

libbfd.idl : bfdarch.idl

bfdarch.idl : /usr/include/bfd.h
	 $(CPP) $< | awk 'BEGIN { go=0; } /^enum bfd_architecture$$/ { go=1; } \
		go && $$0 != "" { print; } \
		/};$$/ { go=0; }' > $@

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



include $(OCAMLMAKEFILE)

bap.dot: $(DOC_FILES)
	 ocamlfind ocamldoc -package str,ocamlgraph,unix -dot -o bap.dot -m avlsoper $(DOC_FILES)
