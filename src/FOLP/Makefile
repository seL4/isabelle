#########################################################################
#									#
# 			Makefile for Isabelle (FOLP)			#
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
FILES =  ROOT.ML ifolp.thy ifolp.ML folp.thy folp.ML intprover.ML simpdata.ML\
	 classical.ML ../Provers/simp.ML ../Provers/ind.ML

EX_FILES = ex/ROOT.ML ex/cla.ML ex/foundn.ML ex/if.ML ex/if.thy ex/int.ML\
	   ex/intro.ML ex/nat.ML ex/nat.thy ex/prolog.ML ex/prolog.thy\
	   ex/prop.ML ex/quant.ML

$(BIN)/FOLP:   $(BIN)/Pure  $(FILES) 
	case "$(COMP)" in \
	poly*)	echo 'make_database"$(BIN)/FOLP"; quit();'  \
			| $(COMP) $(BIN)/Pure;\
		echo 'open PolyML; use"ROOT";' | $(COMP) $(BIN)/FOLP;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/FOLP" banner;' | $(BIN)/Pure;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

$(BIN)/Pure:
	cd ../Pure;  $(MAKE)

test:   ex/ROOT.ML  $(BIN)/FOLP  $(EX_FILES) 
	case "$(COMP)" in \
	poly*)	echo 'use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/FOLP ;;\
	sml*)	echo 'use"ex/ROOT.ML";' | $(BIN)/FOLP;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

.PRECIOUS:   $(BIN)/Pure  $(BIN)/FOLP 
