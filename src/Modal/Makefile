# $Id$
#########################################################################
#									#
# 			Makefile for Isabelle (Modal)			#
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

#Makes LK if this file is ABSENT -- but not 
#if it is out of date, since this Makefile does not know its dependencies!

BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)
FILES = ROOT.ML Modal0.thy prover.ML T.thy S4.thy S43.thy
EX_FILES = ex/ROOT.ML ex/S43thms.ML ex/S4thms.ML ex/Tthms.ML

#Uses cp rather than make_database because Poly/ML allows only 3 levels
$(BIN)/Modal:   $(BIN)/LK  $(FILES) 
	case "$(COMP)" in \
	poly*)	cp $(BIN)/LK $(BIN)/Modal;\
                if [ "$${MAKE_HTML}" = "true" ]; \
                then echo 'open PolyML; make_html := true; exit_use_dir".";' \
                       | $(COMP) $(BIN)/Modal;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
                then echo 'open PolyML; make_html := true; exit_use_dir".";                               make_html := false;' | $(COMP) $(BIN)/Modal;\
                else echo 'open PolyML; exit_use_dir".";' \
		       | $(COMP) $(BIN)/Modal;\
                fi;;\
	sml*)	if [ "$${MAKE_HTML}" = "true" ]; \
                then echo 'make_html := true; exit_use_dir".";                                            xML"$(BIN)/Modal" banner;' | $(BIN)/LK;\
                elif [ "$${MAKE_HTML-undefined}" != "undefined" ];\
                then echo 'make_html := true; exit_use_dir".";                                            make_html := false; xML"$(BIN)/Modal" banner;' \
                       | $(BIN)/LK;\
                else echo 'exit_use_dir"."; xML"$(BIN)/Modal" banner;' \
                       | $(BIN)/LK;\
                fi;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

$(BIN)/LK:
	cd ../LK;  $(MAKE)

test:   ex/ROOT.ML  $(BIN)/Modal  $(EX_FILES)
	case "$(COMP)" in \
	poly*)	echo 'exit_use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/Modal ;;\
	sml*)	echo 'exit_use"ex/ROOT.ML";' | $(BIN)/Modal;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:  $(BIN)/LK $(BIN)/Modal 
