#########################################################################
#									#
# 			Makefile for Isabelle (CHOL)			#
#									#
#########################################################################

#To make the system, cd to this directory and type  
#	make -f Makefile 
#To make the system and test it on standard examples, type  
#	make -f Makefile test

#Environment variable ISABELLECOMP specifies the compiler.
#Environment variable ISABELLEBIN specifies the destination directory.
#For Poly/ML, ISABELLEBIN must begin with a /

#Makes pure Isabelle (Pure) if this file is ABSENT -- but not 
#if it is out of date, since this Makefile does not know its dependencies!

BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)
THYS = HOL.thy Ord.thy Set.thy Fun.thy subset.thy \
       equalities.thy Prod.thy Trancl.thy Sum.thy WF.thy \
       mono.thy Lfp.thy Gfp.thy Nat.thy Inductive.thy \
       Finite.thy Arith.thy Sexp.thy Univ.thy List.thy 

FILES = ROOT.ML add_ind_def.ML datatype.ML hologic.ML\
	ind_syntax.ML indrule.ML intr_elim.ML simpdata.ML\
	subtype.ML thy_syntax.ML ../Pure/section_utils.ML\
	../Provers/hypsubst.ML ../Provers/classical.ML\
        ../Provers/simplifier.ML ../Provers/splitter.ML\
        $(THYS) $(THYS:.thy=.ML)

$(BIN)/CHOL:   $(BIN)/Pure  $(FILES) 
	if [ -d $${ISABELLEBIN:?}/Pure ];\
           	then echo Bad value for ISABELLEBIN: \
                	$(BIN) is the Isabelle source directory; \
                	exit 1; \
           	fi;\
	case "$(COMP)" in \
	poly*)	echo 'make_database"$(BIN)/CHOL"; quit();'  \
			| $(COMP) $(BIN)/Pure;\
		echo 'open PolyML; use"ROOT";' | $(COMP) $(BIN)/CHOL ;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/CHOL" banner;' | $(BIN)/Pure ;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml; exit 1;;\
	esac

$(BIN)/Pure:
	cd ../Pure;  $(MAKE)

#### Testing of CHOL

#A macro referring to the object-logic (depends on ML compiler)
LOGIC:sh=case $ISABELLECOMP in \
	poly*)	echo "$ISABELLECOMP $ISABELLEBIN/CHOL" ;;\
	sml*)	echo "$ISABELLEBIN/CHOL" ;;\
	*)	echo "echo Bad value for ISABELLECOMP: \
                	$ISABELLEBIN is not poly or sml; exit 1" ;;\
	esac

##IMP-semantics example
IMP_THYS = IMP/Com.thy IMP/Denotation.thy IMP/Equiv.thy IMP/Properties.thy
IMP_FILES = IMP/ROOT.ML $(IMP_THYS) $(IMP_THYS:.thy=.ML)

IMP:    $(BIN)/CHOL  $(IMP_FILES)
	echo 'use"IMP/ROOT.ML";quit();' | $(LOGIC)

##The integers in CHOL
INTEG_THYS = Integ/Relation.thy Integ/Equiv.thy Integ/Integ.thy 

INTEG_FILES = Integ/ROOT.ML $(INTEG_THYS) $(INTEG_THYS:.thy=.ML)

Integ:  $(BIN)/CHOL  $(INTEG_FILES)
	echo 'use"Integ/ROOT.ML";quit();' | $(LOGIC)

##I/O Automata
IOA_THYS = IOA/example/Action.thy IOA/example/Channels.thy\
	   IOA/example/Correctness.thy IOA/example/Impl.thy \
	   IOA/example/Lemmas.thy IOA/example/Multiset.thy \
	   IOA/example/Receiver.thy IOA/example/Sender.thy \
	   IOA/meta_theory/Asig.thy IOA/meta_theory/IOA.thy \
	   IOA/meta_theory/Option.thy IOA/meta_theory/Solve.thy

IOA_FILES = IOA/ROOT.ML IOA/example/Packet.thy IOA/example/Spec.thy\
	    $(IOA_THYS) $(IOA_THYS:.thy=.ML)

IOA:    $(BIN)/CHOL  $(IOA_FILES)
	echo 'use"IOA/ROOT.ML";quit();' | $(LOGIC)

##Properties of substitutions
SUBST_THYS = Subst/AList.thy Subst/Setplus.thy\
	     Subst/Subst.thy Subst/Unifier.thy\
	     Subst/UTerm.thy Subst/UTLemmas.thy

SUBST_FILES = Subst/ROOT.ML $(SUBST_THYS) $(SUBST_THYS:.thy=.ML)

Subst:  $(BIN)/CHOL  $(SUBST_FILES)
	echo 'use"Subst/ROOT.ML";quit();' | $(LOGIC)

##Miscellaneous examples
EX_THYS = ex/LexProd.thy ex/MT.thy ex/Acc.thy \
	  ex/PropLog.thy ex/Puzzle.thy ex/Qsort.thy ex/LList.thy \
	  ex/Rec.thy ex/Simult.thy ex/Term.thy ex/String.thy 

EX_FILES = ex/ROOT.ML ex/cla.ML ex/meson.ML ex/mesontest.ML ex/rel.ML \
           ex/set.ML $(EX_THYS) $(EX_THYS:.thy=.ML)

ex:     $(BIN)/CHOL  $(EX_FILES)
	echo 'use"ex/ROOT.ML";quit();' | $(LOGIC)

#Full test.
test:   $(BIN)/CHOL IMP Integ IOA Subst ex
	echo 'Test examples ran successfully' > test

.PRECIOUS:  $(BIN)/Pure $(BIN)/CHOL 
