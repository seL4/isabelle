#########################################################################
#									#
# 			Makefile for Isabelle (LCF)			#
#									#
#########################################################################

#To make the system, cd to this directory and type  
#	make 
#To make the system and test it on standard examples, type  
#	make test

#Environment variable ISABELLECOMP specifies the compiler.
#Environment variable ISABELLEBIN specifies the destination directory.
#For Poly/ML, ISABELLEBIN must begin with a /

#Makes FOL if this file is ABSENT -- but not 
#if it is out of date, since this Makefile does not know its dependencies!

BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)
FILES =  ROOT.ML LCF.thy LCF.ML simpdata.ML pair.ML fix.ML

#Uses cp rather than make_database because Poly/ML allows only 3 levels
$(BIN)/LCF:   $(BIN)/FOL  $(FILES) 
	case "$(COMP)" in \
	poly*)	cp $(BIN)/FOL $(BIN)/LCF;\
		echo 'open PolyML; use"ROOT";' | $(COMP) $(BIN)/LCF ;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/LCF" banner;' | $(BIN)/FOL;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

(BIN)/FOL:
	cd ../FOL;  $(MAKE)

test:   ex.ML  $(BIN)/LCF
	case "$(COMP)" in \
	poly*)	echo 'use"ex.ML"; quit();' | $(COMP) $(BIN)/LCF ;;\
	sml*)	echo 'use"ex.ML";' | $(BIN)/LCF;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:   $(BIN)/FOL  $(BIN)/LCF 
