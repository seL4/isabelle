#########################################################################
#									#
# 			Makefile for Isabelle (FOL)			#
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
FILES =  ROOT.ML IFOL.thy IFOL.ML FOL.thy FOL.ML intprover.ML simpdata.ML \
	../Provers/classical.ML ../Provers/simplifier.ML ../Provers/ind.ML

EX_FILES = ex/ROOT.ML ex/cla.ML ex/foundn.ML ex/If.ML ex/If.thy ex/int.ML\
	   ex/intro.ML ex/List.ML ex/List.thy ex/Nat.ML ex/Nat.thy\
	   ex/Nat2.ML ex/Nat2.thy ex/Prolog.ML ex/Prolog.thy ex/prop.ML\
	   ex/quant.ML

$(BIN)/FOL:   $(BIN)/Pure  $(FILES) 
	if [ -d $${ISABELLEBIN:?}/Pure ];\
           	then echo Bad value for ISABELLEBIN: \
                	$(BIN) is the Isabelle source directory; \
                	exit 1; \
           	fi;\
	case "$(COMP)" in \
	poly*)	echo 'make_database"$(BIN)/FOL"; quit();'  \
			| $(COMP) $(BIN)/Pure;\
		echo 'open PolyML; use"ROOT";' | $(COMP) $(BIN)/FOL;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/FOL" banner;' | $(BIN)/Pure;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

$(BIN)/Pure:
	cd ../Pure;  $(MAKE)

test:   ex/ROOT.ML  $(BIN)/FOL  $(EX_FILES) 
	case "$(COMP)" in \
	poly*)	echo 'use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/FOL ;;\
	sml*)	echo 'use"ex/ROOT.ML";' | $(BIN)/FOL;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:   $(BIN)/Pure  $(BIN)/FOL 
