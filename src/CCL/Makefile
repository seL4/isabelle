# $Id$
#########################################################################
#									#
# 			Makefile for Isabelle (CCL)			#
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

#Makes FOL if this file is ABSENT -- but not 
#if it is out of date, since this Makefile does not know its dependencies!

BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)

SET_FILES = ROOT.ML Set.thy Set.ML subset.ML equalities.ML mono.ML \
	    Gfp.thy Gfp.ML Lfp.thy Lfp.ML

CCL_FILES = CCL.thy CCL.ML Term.thy Term.ML Type.thy Type.ML \
            coinduction.ML Hered.thy Hered.ML Trancl.thy Trancl.ML\
            Wfd.thy Wfd.ML genrec.ML typecheck.ML eval.ML Fix.thy Fix.ML

EX_FILES = ex/ROOT.ML ex/Flag.ML ex/Flag.thy ex/List.ML ex/List.thy\
	   ex/Nat.ML ex/Nat.thy ex/Stream.ML ex/Stream.thy

#Uses cp rather than make_database because Poly/ML allows only 3 levels
$(BIN)/CCL:   $(BIN)/FOL  $(SET_FILES)  $(CCL_FILES) 
	case "$(COMP)" in \
	poly*)	cp $(BIN)/FOL $(BIN)/CCL;\
                if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
                then echo 'open PolyML; init_html (); exit_use"ROOT";' \
                       | $(COMP) $(BIN)/CCL;\
		else echo 'open PolyML; exit_use"ROOT";' | $(COMP) $(BIN)/CCL;\
                fi;;\
	sml*)	if [ "$${MAKE_HTML-undefined}" != "undefined" ];\
                then echo 'init_html (); exit_use"ROOT.ML";                                               xML"$(BIN)/CCL" banner;' | $(BIN)/FOL;\
                else echo 'exit_use"ROOT.ML"; xML"$(BIN)/CCL" banner;' \
                       | $(BIN)/FOL;\
                fi;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

$(BIN)/FOL:
	cd ../FOL;  $(MAKE)

test:   ex/ROOT.ML  $(BIN)/CCL  $(EX_FILES)
	case "$(COMP)" in \
	poly*)	echo 'exit_use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/CCL ;;\
	sml*)	echo 'exit_use"ex/ROOT.ML";' | $(BIN)/CCL;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:  $(BIN)/FOL $(BIN)/CCL 
