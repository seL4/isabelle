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
FILES = ROOT.ML ZF.thy ZF.ML upair.thy upair.ML subset.thy subset.ML \
	pair.thy pair.ML domrange.thy domrange.ML \
	func.thy func.ML AC.thy AC.ML simpdata.thy simpdata.ML\
	equalities.thy equalities.ML Bool.thy Bool.ML \
	Sum.thy Sum.ML QPair.thy QPair.ML mono.ML Fixedpt.thy Fixedpt.ML \
	ind_syntax.thy ind_syntax.ML add_ind_def.thy add_ind_def.ML \
	intr_elim.thy intr_elim.ML indrule.thy indrule.ML \
	inductive.thy inductive.ML \
	Perm.thy Perm.ML Rel.thy Rel.ML EquivClass.ML EquivClass.thy \
	Trancl.thy Trancl.ML \
	WF.thy WF.ML Order.thy Order.ML Ordinal.thy Ordinal.ML \
	Epsilon.thy Epsilon.ML Arith.thy Arith.ML Univ.thy Univ.ML \
	QUniv.thy QUniv.ML constructor.ML Datatype.thy Datatype.ML  \
	OrderArith.thy OrderArith.ML OrderType.thy OrderType.ML \
	Cardinal.thy Cardinal.ML CardinalArith.thy CardinalArith.ML \
	Cardinal_AC.thy Cardinal_AC.ML InfDatatype.thy InfDatatype.ML \
	Zorn.thy Zorn.ML Nat.thy Nat.ML Finite.thy Finite.ML \
	List.thy List.ML

IMP_FILES = IMP/ROOT.ML IMP/Com.ML IMP/Com.thy IMP/Denotation.ML\
            IMP/Denotation.thy IMP/Equiv.ML IMP/Equiv.thy

EX_FILES = ex/ROOT.ML ex/misc.ML ex/Ramsey.ML ex/Ramsey.thy\
	   ex/Integ.ML ex/Integ.thy\
           ex/twos_compl.ML ex/Bin.thy ex/Bin.ML\
	   ex/BT.thy ex/BT.ML ex/Term.thy ex/Term.ML \
	   ex/TF.thy ex/TF.ML ex/Ntree.thy ex/Ntree.ML \
           ex/Brouwer.thy ex/Brouwer.ML \
	   ex/Data.thy ex/Data.ML ex/Enum.thy ex/Enum.ML \
	   ex/Rmap.thy ex/Rmap.ML ex/PropLog.ML ex/PropLog.thy \
	   ex/ListN.thy ex/ListN.ML ex/Acc.thy ex/Acc.ML\
	   ex/Comb.thy ex/Comb.ML ex/Primrec.thy ex/Primrec.ML\
           ex/LList.thy ex/LList.ML ex/CoUnit.thy ex/CoUnit.ML

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

#Directory IMP also tests the system
#Load ex/ROOT.ML last since it creates the file "test"
test:   $(BIN)/ZF  $(IMP_FILES) $(EX_FILES)
	case "$(COMP)" in \
	poly*)	echo 'use"IMP/ROOT.ML"; use"ex/ROOT.ML"; quit();' | \
			$(COMP) $(BIN)/ZF ;;\
	sml*)	echo 'use"IMP/ROOT.ML"; use"ex/ROOT.ML";' | $(BIN)/ZF;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:  $(BIN)/FOL $(BIN)/ZF 
