#########################################################################
#									#
# 			Makefile for Isabelle (FOLP)			#
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
FILES =  ROOT.ML IFOLP.thy IFOLP.ML FOLP.thy FOLP.ML intprover.ML simpdata.ML\
	 classical.ML ../Provers/simp.ML ../Provers/ind.ML

EX_FILES = ex/ROOT.ML ex/cla.ML ex/foundn.ML ex/If.ML ex/If.thy ex/int.ML\
	   ex/intro.ML ex/Nat.ML ex/Nat.thy ex/Prolog.ML ex/Prolog.thy\
	   ex/prop.ML ex/quant.ML

$(BIN)/FOLP:   $(BIN)/Pure  $(FILES) 
	case "$(COMP)" in \
	poly*)	echo 'make_database"$(BIN)/FOLP"; quit();'  \
			| $(COMP) $(BIN)/Pure;\
		echo 'open PolyML; exit_use"ROOT";' | $(COMP) $(BIN)/FOLP;;\
	sml*)	echo 'exit_use"ROOT.ML"; xML"$(BIN)/FOLP" banner;' | $(BIN)/Pure;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

$(BIN)/Pure:
	cd ../Pure;  $(MAKE)

test:   ex/ROOT.ML  $(BIN)/FOLP  $(EX_FILES) 
	case "$(COMP)" in \
	poly*)	echo 'exit_use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/FOLP ;;\
	sml*)	echo 'exit_use"ex/ROOT.ML";' | $(BIN)/FOLP;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:   $(BIN)/Pure  $(BIN)/FOLP 
