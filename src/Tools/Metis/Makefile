###############################################################################
# METIS MAKEFILE
# Copyright (c) 2001 Joe Hurd, distributed under the GNU GPL version 2
###############################################################################

.SUFFIXES:

###############################################################################
# The default action.
###############################################################################

.PHONY: default
default: mosml

###############################################################################
# Cleaning temporary files.
###############################################################################

TEMP = \
  $(MOSML_TARGETS) \
  bin/mosml/*.sml bin/mosml/*.ui bin/mosml/*.uo bin/mosml/a.out \
  $(MLTON_TARGETS) \
  bin/mlton/*.sml bin/mlton/*.mlb \
  $(POLYML_TARGETS) \
  bin/polyml/*.sml bin/polyml/*.o

.PHONY: clean
clean:
	@echo
	@echo '********************'
	@echo '* Clean everything *'
	@echo '********************'
	@echo
	rm -f $(TEMP)
	$(MAKE) -C test $@

###############################################################################
# Testing.
###############################################################################

.PHONY: test
test:
	$(MAKE) -C test

###############################################################################
# Source files.
###############################################################################

SRC = \
  src/Useful.sig src/Useful.sml \
  src/Lazy.sig src/Lazy.sml \
  src/Ordered.sig src/Ordered.sml \
  src/Map.sig src/Map.sml \
  src/KeyMap.sig src/KeyMap.sml \
  src/Set.sig src/Set.sml \
  src/ElementSet.sig src/ElementSet.sml \
  src/Sharing.sig src/Sharing.sml \
  src/Stream.sig src/Stream.sml \
  src/Heap.sig src/Heap.sml \
  src/Print.sig src/Print.sml \
  src/Parse.sig src/Parse.sml \
  src/Name.sig src/Name.sml \
  src/NameArity.sig src/NameArity.sml \
  src/Term.sig src/Term.sml \
  src/Subst.sig src/Subst.sml \
  src/Atom.sig src/Atom.sml \
  src/Formula.sig src/Formula.sml \
  src/Literal.sig src/Literal.sml \
  src/Thm.sig src/Thm.sml \
  src/Proof.sig src/Proof.sml \
  src/Rule.sig src/Rule.sml \
  src/Normalize.sig src/Normalize.sml \
  src/Model.sig src/Model.sml \
  src/Problem.sig src/Problem.sml \
  src/TermNet.sig src/TermNet.sml \
  src/AtomNet.sig src/AtomNet.sml \
  src/LiteralNet.sig src/LiteralNet.sml \
  src/Subsume.sig src/Subsume.sml \
  src/KnuthBendixOrder.sig src/KnuthBendixOrder.sml \
  src/Rewrite.sig src/Rewrite.sml \
  src/Units.sig src/Units.sml \
  src/Clause.sig src/Clause.sml \
  src/Active.sig src/Active.sml \
  src/Waiting.sig src/Waiting.sml \
  src/Resolution.sig src/Resolution.sml \
  src/Tptp.sig src/Tptp.sml \
  src/Options.sig src/Options.sml

EXTRA_SRC = \
  src/problems.sml

###############################################################################
# The ML preprocessor.
###############################################################################

MLPP = scripts/mlpp

MLPP_OPTS =

###############################################################################
# Building using Moscow ML.
###############################################################################

MOSMLC = mosmlc -toplevel -q

MOSML_SRC = \
  src/Portable.sig src/PortableMosml.sml \
  $(SRC)

MOSML_TARGETS = \
  bin/mosml/problems2tptp \
  bin/mosml/metis

include bin/mosml/Makefile.src

.PHONY: mosml-info
mosml-info:
	@echo
	@echo '*****************************************'
	@echo '* Build and test the Moscow ML programs *'
	@echo '*****************************************'
	@echo

.PHONY: mosml
mosml: mosml-info $(MOSML_OBJ) $(MOSML_TARGETS) test

###############################################################################
# Building using MLton.
###############################################################################

MLTON = mlton

MLTON_OPTS = -runtime 'ram-slop 0.4'

MLTON_SRC = \
  src/Portable.sig src/PortableMlton.sml \
  $(SRC)

METIS = bin/mlton/metis

MLTON_TARGETS = \
  bin/mlton/selftest \
  bin/mlton/problems2tptp \
  $(METIS)

bin/mlton/%.sml: $(MLTON_SRC) src/%.sml
	@$(MLPP) $(MLPP_OPTS) -c mlton $^ > $@

bin/mlton/%.mlb: bin/mlton/%.sml
	echo '$$(SML_LIB)/basis/basis.mlb $$(SML_LIB)/basis/mlton.mlb $(notdir $<)' > $@

bin/mlton/%: bin/mlton/%.mlb
	@echo
	@echo '***************************'
	@echo '* Compile a MLton program *'
	@echo '***************************'
	@echo
	@echo $@
	cd bin/mlton ; $(MLTON) $(MLTON_OPTS) $(notdir $<)
	@echo

.PHONY: mlton-info
mlton-info:
	@echo
	@echo '*************************************'
	@echo '* Build and test the MLton programs *'
	@echo '*************************************'
	@echo

.PHONY: mlton
mlton: mlton-info $(MLTON_TARGETS)
	$(MAKE) -C test mlton

###############################################################################
# Building using Poly/ML.
###############################################################################

POLYML = poly

POLYML_OPTS =

POLYML_SRC = \
  src/Random.sig src/Random.sml \
  src/Portable.sig src/PortablePolyml.sml \
  $(SRC)

POLYML_TARGETS = \
  bin/polyml/selftest \
  bin/polyml/problems2tptp \
  bin/polyml/metis

bin/polyml/%.sml: src/%.sml $(POLYML_SRC)
	@$(MLPP) $(MLPP_OPTS) -c polyml $(POLYML_SRC) > $@
	@echo 'fun main () = let' >> $@
	@$(MLPP) $(MLPP_OPTS) -c polyml $< >> $@
	@echo "in () end; PolyML.export(\"$(basename $(notdir $<))\", main);" >> $@

bin/polyml/%.o: bin/polyml/%.sml
	cd bin/polyml ; echo "use \"$(notdir $<)\";" | $(POLYML) $(POLYML_OPTS)

bin/polyml/%: bin/polyml/%.o
	@echo
	@echo '*****************************'
	@echo '* Compile a Poly/ML program *'
	@echo '*****************************'
	@echo
	@echo $@
	cd bin/polyml && $(CC) -o $(notdir $@) $(notdir $<) -lpolymain -lpolyml
	@echo

.PHONY: polyml-info
polyml-info:
	@echo
	@echo '***************************************'
	@echo '* Build and test the Poly/ML programs *'
	@echo '***************************************'
	@echo

.PHONY: polyml
polyml: polyml-info $(POLYML_TARGETS)
	$(MAKE) -C test polyml

###############################################################################
# Development.
##############################################################################

include Makefile.dev

Makefile.dev:
	echo > $@
