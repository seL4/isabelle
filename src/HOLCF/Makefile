############################################################################
#                                                                          #
#                   Makefile for Isabelle (HOLCF)                          #
#                                                                          #
############################################################################

#To make the system, cd to this directory and type  
#	make -f Makefile 

#Environment variable ISABELLECOMP specifies the compiler.
#Environment variable ISABELLEBIN specifies the destination directory.
#For Poly/ML, ISABELLEBIN must begin with a /

#Makes HOL Isabelle if this file is ABSENT -- but not 
#if it is out of date, since this Makefile does not know its dependencies!

BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)
FILES = ROOT.ML Void.thy Void.ML Porder.thy Porder.ML Pcpo.thy \
	Pcpo.ML Fun1.thy Fun1.ML Fun2.thy Fun2.ML Fun3.thy Fun3.ML \
	Cfun1.thy Cfun1.ML Cfun2.thy Cfun2.ML Cfun3.thy Cfun3.ML \
	cinfix.ML\
	Sprod0.thy Sprod0.ML Sprod1.thy Sprod1.ML Sprod2.thy Sprod2.ML\
	Sprod3.thy Sprod3.ML

EX_FILES = ex/Coind.thy ex/Coind.ML \
           ex/Hoare.thy ex/Hoare.ML ex/Loop.thy ex/Loop.ML

$(BIN)/HOLCF:   $(BIN)/HOL  $(FILES) 
	case "$(COMP)" in \
	poly*)  echo 'make_database"$(BIN)/HOLCF"; quit();'  \
		     | $(COMP) $(BIN)/HOL ;\
		echo 'use"ROOT";' | $(COMP) $(BIN)/HOLCF ;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/HOLCF" banner;' | $(BIN)/HOL ;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

$(BIN)/HOL:
	cd ../HOL;  $(MAKE)

test:   ex/ROOT.ML  $(BIN)/HOLCF  $(EX_FILES) 
	case "$(COMP)" in \
	poly*)	echo 'use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/HOLCF ;;\
	sml*)	echo 'use"ex/ROOT.ML"' | $(BIN)/HOLCF;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

.PRECIOUS:  $(BIN)/HOL  $(BIN)/HOLCF 

