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
FILES = ROOT.ML Holcfb.thy Holcfb.ML Void.thy Void.ML \
	Porder0.thy Porder.thy Porder.ML  Pcpo.thy \
	Pcpo.ML Fun1.thy Fun1.ML Fun2.thy Fun2.ML Fun3.thy Fun3.ML \
	Cfun1.thy Cfun1.ML Cfun2.thy Cfun2.ML Cfun3.thy Cfun3.ML \
	Cont.thy Cont.ML \
	Cprod1.thy Cprod1.ML Cprod2.thy Cprod2.ML Cprod3.thy Cprod3.ML \
	Sprod0.thy Sprod0.ML Sprod1.thy Sprod1.ML Sprod2.thy Sprod2.ML\
	Sprod3.thy Sprod3.ML\
	Ssum0.thy Ssum0.ML Ssum1.thy Ssum1.ML Ssum2.thy Ssum2.ML\
	Ssum3.thy Ssum3.ML\
	Lift1.thy Lift1.ML Lift2.thy Lift2.ML Lift3.thy Lift3.ML \
	Fix.thy Fix.ML ccc1.thy ccc1.ML One.thy One.ML \
	Tr1.thy Tr1.ML Tr2.thy Tr2.ML HOLCF.thy HOLCF.ML \
	Dnat.thy Dnat.ML Dnat2.thy Dnat2.ML \
	Stream.thy Stream.ML Stream2.thy Stream2.ML Dlist.thy Dlist.ML 

EX_FILES = ex/Coind.thy ex/Coind.ML ex/Hoare.thy ex/Hoare.ML \
           ex/Loop.thy ex/Loop.ML ex/Dagstuhl.thy ex/Dagstuhl.ML 

$(BIN)/HOLCF:   $(BIN)/HOL  $(FILES) 
	case "$(COMP)" in \
	poly*)  echo 'make_database"$(BIN)/HOLCF"; quit();'  \
		     | $(COMP) $(BIN)/HOL ;\
		echo 'use"ROOT";' | $(COMP) $(BIN)/HOLCF ;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/HOLCF" banner;' | $(BIN)/HOL ;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

$(BIN)/HOL:
	cd ../HOL;  $(MAKE)

test:   ex/ROOT.ML  $(BIN)/HOLCF  $(EX_FILES) 
	case "$(COMP)" in \
	poly*)	echo 'use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/HOLCF ;;\
	sml*)	echo 'use"ex/ROOT.ML"' | $(BIN)/HOLCF;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:  $(BIN)/HOL  $(BIN)/HOLCF 

