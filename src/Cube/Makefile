#########################################################################
#									#
# 			Makefile for Isabelle (Cube)			#
#									#
#########################################################################

#To make the system, cd to this directory and type  
#	make 
#To make the system and test it on standard examples, type  
#	make test

#Environment variable ISABELLECOMP specifies the compiler.
#Environment variable ISABELLEBIN specifies the destination directory.
#For Poly/ML, ISABELLEBIN must begin with a /
#WARNING: Poly/ML databases may fail if copied or moved!

#Makes pure Isabelle (Pure) if this file is ABSENT -- but not 
#if it is out of date, since this Makefile does not know its dependencies!

BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)
FILES = 	ROOT.ML  cube.thy  cube.ML

$(BIN)/Cube:   $(BIN)/Pure  $(FILES) 
	case "$(COMP)" in \
	poly*)	echo 'make_database"$(BIN)/Cube"; quit();'  \
			| $(COMP) $(BIN)/Pure;\
		echo 'open PolyML; use"ROOT";' | $(COMP) $(BIN)/Cube ;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/Cube" banner;' | $(BIN)/Pure ;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

$(BIN)/Pure:
	cd ../Pure;  $(MAKE)

test:   ex.ML $(BIN)/Cube
	case "$(COMP)" in \
	poly*)	echo 'use"ex.ML"; quit();' | $(COMP) $(BIN)/Cube ;;\
	sml*)	echo 'use"ex.ML";' | $(BIN)/Cube;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

.PRECIOUS:  $(BIN)/Pure  $(BIN)/Cube 
