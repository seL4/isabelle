#########################################################################
#									#
# 			Makefile for Isabelle (Modal)			#
#									#
#########################################################################

#To make the system, cd to this directory and type
#	make -f Makefile 
#To make the system and test it on standard examples, type 
#	make -f Makefile test

#Environment variable ISABELLECOMP specifies the compiler.
#Environment variable ISABELLEBIN specifies the destination directory.
#For Poly/ML, ISABELLEBIN must begin with a /

#Makes LK if this file is ABSENT -- but not 
#if it is out of date, since this Makefile does not know its dependencies!

BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)
FILES = ROOT.ML modal0.thy prover.ML T.thy S4.thy S43.thy

#Uses cp rather than make_database because Poly/ML allows only 3 levels
$(BIN)/Modal:   $(BIN)/LK  $(FILES) 
	case "$(COMP)" in \
	poly*)	cp $(BIN)/LK $(BIN)/Modal;\
		echo 'open PolyML; use"ROOT";' | $(COMP) $(BIN)/Modal ;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/Modal" banner;' | $(BIN)/LK;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

$(BIN)/LK:
	cd ../LK;  $(MAKE)

test:   ex/ROOT.ML  $(BIN)/Modal
	case "$(COMP)" in \
	poly*)	echo 'use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/Modal ;;\
	sml*)	echo 'use"ex/ROOT.ML";' | $(BIN)/Modal;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

.PRECIOUS:  $(BIN)/LK $(BIN)/Modal 
