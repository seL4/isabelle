#########################################################################
#									#
# 			Makefile for Isabelle (CCL)			#
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

SET_FILES = ROOT.ML set.thy set.ML subset.ML equalities.ML mono.ML \
	    gfp.thy gfp.ML lfp.thy lfp.ML

CCL_FILES = ccl.thy ccl.ML term.thy term.ML type.thy type.ML \
            coinduction.ML hered.thy hered.ML trancl.thy trancl.ML\
            wfd.thy wfd.ML genrec.ML typecheck.ML eval.ML fix.thy fix.ML

EX_FILES = ex/ROOT.ML ex/flag.ML ex/flag.thy ex/list.ML ex/list.thy\
	   ex/nat.ML ex/nat.thy ex/stream.ML ex/stream.thy

#Uses cp rather than make_database because Poly/ML allows only 3 levels
$(BIN)/CCL:   $(BIN)/FOL  $(SET_FILES)  $(CCL_FILES) 
	case "$(COMP)" in \
	poly*)	cp $(BIN)/FOL $(BIN)/CCL;\
		echo 'open PolyML; use"ROOT";' | $(COMP) $(BIN)/CCL ;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/CCL" banner;' | $(BIN)/FOL;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

$(BIN)/FOL:
	cd ../FOL;  $(MAKE)

test:   ex/ROOT.ML  $(BIN)/CCL  $(EX_FILES)
	case "$(COMP)" in \
	poly*)	echo 'use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/CCL ;;\
	sml*)	echo 'use"ex/ROOT.ML";' | $(BIN)/CCL;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

.PRECIOUS:  $(BIN)/FOL $(BIN)/CCL 
