#########################################################################
#									#
# 			Makefile for Isabelle (LK)			#
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
FILES =  ROOT.ML LK.thy LK.ML
EX_FILES = ex/ROOT.ML ex/hardquant.ML ex/prop.ML ex/quant.ML

$(BIN)/LK:   $(BIN)/Pure  $(FILES) 
	case "$(COMP)" in \
	poly*)	echo 'make_database"$(BIN)/LK"; quit();'  \
			| $(COMP) $(BIN)/Pure;\
		echo 'open PolyML; use"ROOT";' | $(COMP) $(BIN)/LK ;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/LK" banner;' | $(BIN)/Pure ;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

$(BIN)/Pure:
	cd ../Pure;  $(MAKE)

test:   ex/ROOT.ML  $(BIN)/LK  $(EX_FILES)
	case "$(COMP)" in \
	poly*)	echo 'use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/LK ;;\
	sml*)	echo 'use"ex/ROOT.ML";' | $(BIN)/LK;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:   $(BIN)/Pure  $(BIN)/LK 
