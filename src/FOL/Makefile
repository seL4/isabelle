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
FILES =  ROOT.ML ifol.thy ifol.ML fol.thy fol.ML int-prover.ML simpdata.ML \
	../Provers/classical.ML ../Provers/simplifier.ML ../Provers/ind.ML

$(BIN)/FOL:   $(BIN)/Pure  $(FILES) 
	case "$(COMP)" in \
	poly*)	echo 'make_database"$(BIN)/FOL"; quit();'  \
			| $(COMP) $(BIN)/Pure;\
		echo 'open PolyML; use"ROOT";' | $(COMP) $(BIN)/FOL;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/FOL" banner;' | $(BIN)/Pure;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

$(BIN)/Pure:
	cd ../Pure;  $(MAKE)

test:   ex/ROOT.ML  $(BIN)/FOL
	case "$(COMP)" in \
	poly*)	echo 'use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/FOL ;;\
	sml*)	echo 'use"ex/ROOT.ML";' | $(BIN)/FOL;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

.PRECIOUS:   $(BIN)/Pure  $(BIN)/FOL 
