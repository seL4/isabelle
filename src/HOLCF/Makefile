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
THYS = Holcfb.thy Void.thy Porder.thy Pcpo.thy \
       Fun1.thy Fun2.thy Fun3.thy \
       Cfun1.thy Cfun2.thy Cfun3.thy Cont.thy \
       Cprod1.thy Cprod2.thy Cprod3.thy \
       Sprod0.thy Sprod1.thy Sprod2.thy Sprod3.thy \
       Ssum0.thy Ssum1.thy Ssum2.thy Ssum3.thy \
       Lift1.thy Lift2.thy Lift3.thy Fix.thy ccc1.thy One.thy \
       Tr1.thy Tr2.thy HOLCF.thy Dnat.thy Dnat2.thy \
       Stream.thy Stream2.thy Dlist.thy 

FILES = ROOT.ML Porder0.thy  $(THYS) $(THYS:.thy=.ML)

$(BIN)/HOLCF:   $(BIN)/HOL  $(FILES) 
	case "$(COMP)" in \
	poly*)  echo 'make_database"$(BIN)/HOLCF"; quit();'  \
		     | $(COMP) $(BIN)/HOL ;\
		echo 'exit_use"ROOT";' | $(COMP) $(BIN)/HOLCF ;;\
	sml*)	echo 'exit_use"ROOT.ML"; xML"$(BIN)/HOLCF" banner;' | $(BIN)/HOL ;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

$(BIN)/HOL:
	cd ../HOL;  $(MAKE)

EX_THYS = ex/Coind.thy ex/Hoare.thy \
           ex/Loop.thy ex/Dagstuhl.thy 

EX_FILES = ex/ROOT.ML ex/loeckx.ML $(EX_THYS) $(EX_THYS:.thy=.ML)

test:   ex/ROOT.ML  $(BIN)/HOLCF  $(EX_FILES) 
	case "$(COMP)" in \
	poly*)	echo 'exit_use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/HOLCF ;;\
	sml*)	echo 'exit_use"ex/ROOT.ML"' | $(BIN)/HOLCF;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:  $(BIN)/HOL  $(BIN)/HOLCF 

