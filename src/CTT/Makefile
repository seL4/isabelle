# $Id$
#########################################################################
#									#
#			Makefile for Isabelle (CTT)			#
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
FILES =		ROOT.ML CTT.thy CTT.ML Bool.thy Bool.ML \
		Arith.thy Arith.ML rew.ML ../Provers/typedsimp.ML

EX_FILES = ex/ROOT.ML ex/elim.ML ex/equal.ML ex/synth.ML ex/typechk.ML

$(BIN)/CTT:   $(BIN)/Pure  $(FILES) 
	if [ -d $${ISABELLEBIN:?}/Pure ];\
		then echo Bad value for ISABELLEBIN: \
			$(BIN) is the Isabelle source directory; \
			exit 1; \
		fi;\
	case "$(COMP)" in \
	poly*)	echo 'make_database"$(BIN)/CTT"; quit();'  \
			| $(COMP) $(BIN)/Pure;\
		if [ "$${MAKE_HTML}" = "true" ]; \
		then echo 'open PolyML; make_html := true; exit_use_dir".";' \
		       | $(COMP) $(BIN)/CTT;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
		then echo 'open PolyML; make_html := true; exit_use_dir".";				  make_html := false;' | $(COMP) $(BIN)/CTT;\
		else echo 'open PolyML; exit_use_dir".";' \
		       | $(COMP) $(BIN)/CTT;\
		fi;\
		discgarb -c $(BIN)/CTT;;\
	sml*)	if [ "$${MAKE_HTML}" = "true" ]; \
		then echo 'make_html := true; exit_use_dir".";						  xML"$(BIN)/CTT" banner;' | $(BIN)/Pure;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ];\
		then echo 'make_html := true; exit_use_dir".";						  make_html := false; xML"$(BIN)/CTT" banner;' \
		       | $(BIN)/Pure;\
		else echo 'exit_use_dir"."; xML"$(BIN)/CTT" banner;' \
		       | $(BIN)/Pure;\
		fi;;\
	*)	echo Bad value for ISABELLECOMP: \
			$(COMP) is not poly or sml;;\
	esac

$(BIN)/Pure:
	cd ../Pure;  $(MAKE)

test:	ex/ROOT.ML $(BIN)/CTT  $(EX_FILES) 
	case "$(COMP)" in \
	poly*)	echo 'exit_use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/CTT ;;\
	sml*)	echo 'exit_use"ex/ROOT.ML";' | $(BIN)/CTT;;\
	*)	echo Bad value for ISABELLECOMP: \
			$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:  $(BIN)/Pure	 $(BIN)/CTT 
