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
FILES = ROOT.ML void.thy void.ML porder.thy porder.ML pcpo.thy \
	pcpo.ML fun1.thy fun1.ML fun2.thy fun2.ML fun3.thy fun3.ML \
	cfun1.thy cfun1.ML cfun2.thy cfun2.ML cfun3.thy cfun3.ML \
	cinfix.ML\
	sprod0.thy sprod0.ML sprod1.thy sprod1.ML sprod2.thy sprod2.ML\
	sprod3.thy sprod3.ML

EX_FILES = ex/coind.thy ex/coind.ML \
           ex/hoare.thy ex/hoare.ML ex/loop.thy ex/loop.ML

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

