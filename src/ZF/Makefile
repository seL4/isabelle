#########################################################################
#									#
# 			Makefile for Isabelle (ZF)			#
#									#
#########################################################################

#To make the system, cd to this directory and type
#	make -f Makefile 
#To make the system and test it on standard examples, type 
#	make -f Makefile test

#Environment variable ISABELLECOMP specifies the compiler.
#Environment variable ISABELLEBIN specifies the destination directory.
#For Poly/ML, ISABELLEBIN must begin with a /

#Makes FOL if this file is ABSENT -- but not 
#if it is out of date, since this Makefile does not know its dependencies!

BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)
FILES = ROOT.ML ZF.thy ZF.ML upair.ML subset.ML pair.ML domrange.ML \
	func.ML simpdata.ML Bool.thy Bool.ML \
	Sum.thy Sum.ML Qpair.thy Qpair.ML mono.ML Fixedpt.thy Fixedpt.ML \
	ind_syntax.ML intr_elim.ML indrule.ML inductive.ML coinductive.ML \
	equalities.ML Perm.thy Perm.ML Trancl.thy Trancl.ML \
	WF.thy WF.ML Ord.thy Ord.ML Nat.thy Nat.ML \
	Epsilon.thy Epsilon.ML Arith.thy Arith.ML Univ.thy Univ.ML \
	Quniv.thy Quniv.ML constructor.ML datatype.ML  \
	fin.ML list.ML ListFn.thy ListFn.ML

EX_FILES = ex/ROOT.ML ex/acc.ML ex/bin.ML ex/BinFn.ML ex/BinFn.thy\
	   ex/BT.ML ex/BT_Fn.ML ex/BT_Fn.thy ex/comb.ML\
	   ex/Contract0.ML ex/Contract0.thy ex/counit.ML ex/data.ML\
	   ex/enum.ML ex/Equiv.ML ex/Equiv.thy ex/Integ.ML ex/Integ.thy\
	   ex/listn.ML ex/llist.ML ex/llist_eq.ML ex/LListFn.ML ex/LListFn.thy\
	   ex/misc.ML ex/parcontract.ML ex/Primrec0.ML ex/Primrec0.thy\
	   ex/prop.ML ex/PropLog.ML ex/PropLog.thy ex/Ramsey.ML ex/Ramsey.thy\
	   ex/rmap.ML ex/term.ML ex/TermFn.ML ex/TermFn.thy ex/tf.ML\
	   ex/TF_Fn.ML ex/TF_Fn.thy ex/twos_compl.ML

#Uses cp rather than make_database because Poly/ML allows only 3 levels
$(BIN)/ZF:   $(BIN)/FOL  $(FILES) 
	case "$(COMP)" in \
	poly*)	cp $(BIN)/FOL $(BIN)/ZF;\
		echo 'open PolyML; use"ROOT";' | $(COMP) $(BIN)/ZF ;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/ZF" banner;' | $(BIN)/FOL;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

$(BIN)/FOL:
	cd ../FOL;  $(MAKE)

test:   ex/ROOT.ML  $(BIN)/ZF  $(EX_FILES)
	case "$(COMP)" in \
	poly*)	echo 'use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/ZF ;;\
	sml*)	echo 'use"ex/ROOT.ML";' | $(BIN)/ZF;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

.PRECIOUS:  $(BIN)/FOL $(BIN)/ZF 
