#########################################################################
#									#
# 			Makefile for Isabelle (CTT)			#
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
FILES = 	ROOT.ML ctt.thy ctt.ML bool.thy bool.ML \
		arith.thy arith.ML rew.ML ../Provers/typedsimp.ML

$(BIN)/CTT:   $(BIN)/Pure  $(FILES) 
	case "$(COMP)" in \
	poly*)	echo 'make_database"$(BIN)/CTT"; quit();'  \
			| $(COMP) $(BIN)/Pure;\
		echo 'open PolyML; use"ROOT";' | $(COMP) $(BIN)/CTT ;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/CTT" banner;' | $(BIN)/Pure ;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

$(BIN)/Pure:
	cd ../Pure;  $(MAKE)

test:   ex/ROOT.ML $(BIN)/CTT
	case "$(COMP)" in \
	poly*)	echo 'use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/CTT ;;\
	sml*)	echo 'use"ex/ROOT.ML";' | $(BIN)/CTT;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

.PRECIOUS:  $(BIN)/Pure  $(BIN)/CTT 
