# $Id$
#########################################################################
#									#
# 			Makefile for Isabelle (Sequents)		#
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

#Makes Pure if this file is ABSENT -- but not 
#if it is out of date, since this Makefile does not know its dependencies!

BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)
NAMES = ILL LK S4 S43 T
FILES = ROOT.ML Sequents.thy prover.ML $(NAMES:%=%.thy) $(NAMES:%=%.ML)

ILL_NAMES = ILL_predlog washing 
EX_FILES = ex/ROOT.ML \
    ex/LK/ROOT.ML ex/LK/hardquant.ML ex/LK/prop.ML ex/LK/quant.ML \
    ex/Modal/ROOT.ML ex/Modal/S43thms.ML ex/Modal/S4thms.ML ex/Modal/Tthms.ML \
    ex/ILL/ILL_kleene_lemmas.ML \
    $(ILL_NAMES:%=ex/ILL/%.thy) $(ILL_NAMES:%=ex/ILL/%.ML)

$(BIN)/Sequents:   $(BIN)/Pure  $(FILES) 
	case "$(COMP)" in \
	poly*)	echo 'make_database"$(BIN)/Sequents"; quit();'  \
			| $(COMP) $(BIN)/Pure;\
                if [ "$${MAKE_HTML}" = "true" ]; \
                then echo 'open PolyML; make_html := true; exit_use_dir".";' \
                       | $(COMP) $(BIN)/Sequents;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
                then echo 'open PolyML; make_html := true; exit_use_dir".";                               make_html := false;' | $(COMP) $(BIN)/Sequents;\
                else echo 'open PolyML; exit_use_dir".";' | $(COMP) $(BIN)/Sequents;\
                fi;\
		discgarb -c $(BIN)/Sequents;;\
	sml*)	if [ "$${MAKE_HTML}" = "true" ]; \
                then echo 'make_html := true; exit_use_dir".";                                            xML"$(BIN)/Sequents" banner;' | $(BIN)/Pure;\
                elif [ "$${MAKE_HTML-undefined}" != "undefined" ];\
                then echo 'make_html := true; exit_use_dir".";                                            make_html := false; xML"$(BIN)/Sequents" banner;' \
                       | $(BIN)/Pure;\
                else echo 'exit_use_dir"."; xML"$(BIN)/Sequents" banner;' \
                       | $(BIN)/Pure;\
                fi;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

$(BIN)/Pure:
	cd ../Pure;  $(MAKE)

test:   $(BIN)/Sequents  $(EX_FILES)
	case "$(COMP)" in \
	poly*)	echo 'exit_use"ex/ROOT.ML";quit();' | $(COMP) $(BIN)/Sequents;;\
	sml*)	echo 'exit_use"ex/ROOT.ML";' | $(BIN)/Sequents;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac




.PRECIOUS:  $(BIN)/Pure $(BIN)/Sequents 
