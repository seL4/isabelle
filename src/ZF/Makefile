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
THYS = ZF.thy upair.thy subset.thy pair.thy domrange.thy \
       func.thy AC.thy simpdata.thy equalities.thy Bool.thy \
       Sum.thy QPair.thy mono.thy Fixedpt.thy ind_syntax.thy add_ind_def.thy \
       constructor.thy intr_elim.thy indrule.thy Inductive.thy \
       Perm.thy Rel.thy EquivClass.thy Trancl.thy \
       WF.thy Order.thy Ordinal.thy Epsilon.thy Arith.thy Univ.thy \
       QUniv.thy Datatype.thy OrderArith.thy OrderType.thy \
       Cardinal.thy CardinalArith.thy Cardinal_AC.thy InfDatatype.thy \
       Zorn.thy Nat.thy Finite.thy List.thy 

FILES = ROOT.ML thy_syntax.ML ../Pure/section_utils.ML $(THYS) $(THYS:.thy=.ML)
	

#Uses cp rather than make_database because Poly/ML allows only 3 levels
$(BIN)/ZF:   $(BIN)/FOL  $(FILES) 
	case "$(COMP)" in \
	poly*)	cp $(BIN)/FOL $(BIN)/ZF;\
		echo 'open PolyML; use"ROOT";' | $(COMP) $(BIN)/ZF ;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/ZF" banner;' | $(BIN)/FOL;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml; exit 1;;\
	esac

$(BIN)/FOL:
	cd ../FOL;  $(MAKE)

#### Testing of ZF

#A macro referring to the object-logic (depends on ML compiler)
LOGIC:sh=case $ISABELLECOMP in \
	poly*)	echo "$ISABELLECOMP $ISABELLEBIN/ZF" ;;\
	sml*)	echo "$ISABELLEBIN/ZF" ;;\
	*)	echo "echo Bad value for ISABELLECOMP: \
                	$ISABELLEBIN is not poly or sml; exit 1" ;;\
	esac

##IMP-semantics example
IMP_THYS = IMP/Com.thy IMP/Denotation.thy IMP/Equiv.thy
IMP_FILES = IMP/ROOT.ML $(IMP_THYS) $(IMP_THYS:.thy=.ML)

IMP:   $(BIN)/ZF  $(IMP_FILES)
	echo 'use"IMP/ROOT.ML";quit();' | $(LOGIC)

##Coinduction example
COIND_THYS = Coind/ECR.thy Coind/Language.thy\
	     Coind/MT.thy Coind/Map.thy Coind/Static.thy \
	     Coind/Types.thy Coind/Values.thy 

COIND_FILES = Coind/ROOT.ML Coind/BCR.thy  Coind/Dynamic.thy \
              $(COIND_THYS) $(COIND_THYS:.thy=.ML)

Coind:  $(BIN)/ZF  $(COIND_FILES)
	echo 'use"Coind/ROOT.ML";quit();' | $(LOGIC)

##Miscellaneous examples
EX_THYS = ex/Ramsey.thy ex/Integ.thy ex/twos_compl.thy ex/Bin.thy \
	  ex/BT.thy ex/Term.thy  ex/TF.thy ex/Ntree.thy \
	  ex/Brouwer.thy ex/Data.thy ex/Enum.thy \
	  ex/Rmap.thy ex/PropLog.thy ex/ListN.thy ex/Acc.thy \
	  ex/Comb.thy ex/Primrec.thy ex/LList.thy ex/CoUnit.thy 
EX_FILES = ex/ROOT.ML ex/misc.ML $(EX_THYS) $(EX_THYS:.thy=.ML)

#Test ZF by loading the examples in directory ex
ex:     $(BIN)/ZF  $(EX_FILES)
	echo 'use"ex/ROOT.ML";quit();' | $(LOGIC)

#Full test.
test:   $(BIN)/ZF IMP Coind ex
	echo 'Test examples ran successfully' > test

.PRECIOUS:  $(BIN)/FOL $(BIN)/ZF 
