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
	Sum.thy Sum.ML QPair.thy QPair.ML mono.ML Fixedpt.thy Fixedpt.ML \
	ind_syntax.ML intr_elim.ML indrule.ML inductive.ML coinductive.ML \
	equalities.ML Perm.thy Perm.ML Rel.thy Rel.ML Trancl.thy Trancl.ML \
	WF.thy WF.ML Order.thy Order.ML Ordinal.thy Ordinal.ML \
	OrderArith.thy OrderArith.ML OrderType.thy OrderType.ML \
	Cardinal.thy Cardinal.ML CardinalArith.thy CardinalArith.ML \
	Nat.thy Nat.ML \
	Epsilon.thy Epsilon.ML Arith.thy Arith.ML Univ.thy Univ.ML \
	QUniv.thy QUniv.ML constructor.ML Datatype.ML  \
	Fin.ML List.ML ListFn.thy ListFn.ML

IMP_FILES = IMP/ROOT.ML IMP/Aexp.ML IMP/Aexp.thy IMP/Assign.ML IMP/Assign.thy\
            IMP/Bexp.ML IMP/Bexp.thy IMP/Com.ML IMP/Com.thy IMP/Denotation.ML\
            IMP/Denotation.thy IMP/Equiv.ML IMP/Equiv.thy IMP/Evala0.thy\
            IMP/Evala.ML IMP/Evala.thy IMP/Evalb0.thy IMP/Evalb.ML\
            IMP/Evalb.thy IMP/Evalc0.thy IMP/Evalc.ML IMP/Evalc.thy

EX_FILES = ex/ROOT.ML ex/Acc.ML ex/Bin.ML ex/BinFn.ML ex/BinFn.thy\
	   ex/BT.ML ex/BT_Fn.ML ex/BT_Fn.thy ex/Comb.ML\
	   ex/Contract0.ML ex/Contract0.thy ex/CoUnit.ML ex/Data.ML\
	   ex/Enum.ML ex/Equiv.ML ex/Equiv.thy ex/Integ.ML ex/Integ.thy\
	   ex/ListN.ML ex/LList.ML ex/LList_Eq.ML ex/LListFn.ML ex/LListFn.thy\
	   ex/misc.ML ex/ParContract.ML ex/Primrec0.ML ex/Primrec0.thy\
	   ex/Prop.ML ex/PropLog.ML ex/PropLog.thy ex/Ramsey.ML ex/Ramsey.thy\
	   ex/Rmap.ML ex/Term.ML ex/TermFn.ML ex/TermFn.thy ex/TF.ML\
	   ex/TF_Fn.ML ex/TF_Fn.thy ex/twos_compl.ML

#Uses cp rather than make_database because Poly/ML allows only 3 levels
$(BIN)/ZF:   $(BIN)/FOL  $(FILES) 
	case "$(COMP)" in \
	poly*)	cp $(BIN)/FOL $(BIN)/ZF;\
		echo 'open PolyML; use"ROOT";' | $(COMP) $(BIN)/ZF ;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/ZF" banner;' | $(BIN)/FOL;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

$(BIN)/FOL:
	cd ../FOL;  $(MAKE)

test:   ex/ROOT.ML  $(BIN)/ZF  $(IMP_FILES) $(EX_FILES)
	case "$(COMP)" in \
	poly*)	echo 'use"IMP/ROOT.ML"; use"ex/ROOT.ML"; quit();' | \
			$(COMP) $(BIN)/ZF ;;\
	sml*)	echo 'use"IMP/ROOT.ML"; use"ex/ROOT.ML";' | $(BIN)/ZF;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:  $(BIN)/FOL $(BIN)/ZF 
