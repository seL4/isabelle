# $Id$
#########################################################################
#									#
#			Makefile for Isabelle (FOL)			#
#									#
#########################################################################

#To make the system, cd to this directory and type  
#	make
#To make the system and test it on standard examples, type  
#	make test
#To generate HTML files for every theory, set the environment variable
#MAKE_HTML or add the parameter "MAKE_HTML=".

#Environment variable ISABELLECOMP specifies the compiler.
#Environment variable ISABELLEBIN specifies the destination directory.
#For Poly/ML, ISABELLEBIN must begin with a /

#Makes pure Isabelle (Pure) if this file is ABSENT -- but not 
#if it is out of date, since this Makefile does not know its dependencies!

BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)
FILES =	 ROOT.ML IFOL.thy IFOL.ML FOL.thy FOL.ML intprover.ML simpdata.ML \
	 ../Provers/hypsubst.ML ../Provers/classical.ML \
	 ../Provers/simplifier.ML ../Provers/splitter.ML ../Provers/ind.ML

EX_NAMES = If List Nat Nat2 Prolog declIffOracle IffOracle
EX_FILES = ex/ROOT.ML ex/cla.ML ex/foundn.ML  ex/int.ML ex/intro.ML\
	   ex/prop.ML ex/quant.ML $(EX_NAMES:%=ex/%.thy) $(EX_NAMES:%=ex/%.ML)

$(BIN)/FOL:   $(BIN)/Pure  $(FILES) 
	if [ -d $${ISABELLEBIN:?}/Pure ];\
		then echo Bad value for ISABELLEBIN: \
			$(BIN) is the Isabelle source directory; \
			exit 1; \
		fi;\
	case "$(COMP)" in \
	poly*)	echo 'make_database"$(BIN)/FOL"; quit();' \
		  | $(COMP) $(BIN)/Pure;\
		if [ "$${MAKE_HTML}" = "true" ]; \
		then echo 'open PolyML; make_html := true; exit_use_dir".";' \
		       | $(COMP) $(BIN)/FOL;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
		then echo 'open PolyML; make_html := true; exit_use_dir".";				  make_html := false;' | $(COMP) $(BIN)/FOL;\
		else echo 'open PolyML; exit_use_dir".";' \
		       | $(COMP) $(BIN)/FOL;\
		fi;\
		discgarb -c $(BIN)/FOL;;\
	sml*)	if [ "$${MAKE_HTML}" = "true" ]; \
		then echo 'make_html := true; exit_use_dir".";						  xML"$(BIN)/FOL" banner;' | $(BIN)/Pure;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ];\
		then echo 'make_html := true; exit_use_dir".";						  make_html := false; xML"$(BIN)/FOL" banner;' \
		       | $(BIN)/Pure;\
		else echo 'exit_use_dir"."; xML"$(BIN)/FOL" banner;' \
		       | $(BIN)/Pure;\
		fi;;\
	*)	echo Bad value for ISABELLECOMP: \
			$(COMP) is not poly or sml;;\
	esac

$(BIN)/Pure:
	cd ../Pure;  $(MAKE)

test:	ex/ROOT.ML  $(BIN)/FOL	$(EX_FILES) 
	case "$(COMP)" in \
	poly*)	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
		then echo 'make_html := true; exit_use_dir"ex"; quit();' \
		       | $(COMP) $(BIN)/FOL;\
		else echo 'exit_use_dir"ex"; quit();' | $(COMP) $(BIN)/FOL;\
		fi;;\
	sml*)	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
		then echo 'make_html := true; exit_use_dir"ex";' \
		       | $(BIN)/FOL;\
		else echo 'exit_use_dir"ex";' | $(BIN)/FOL;\
		fi;;\
	*)	echo Bad value for ISABELLECOMP: \
			$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:   $(BIN)/Pure  $(BIN)/FOL 
