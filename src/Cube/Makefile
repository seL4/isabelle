# $Id$
#########################################################################
#									#
# 			Makefile for Isabelle (Cube)			#
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
#WARNING: Poly/ML databases may fail if copied or moved!

#Makes pure Isabelle (Pure) if this file is ABSENT -- but not 
#if it is out of date, since this Makefile does not know its dependencies!

BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)
FILES = 	ROOT.ML  Cube.thy  Cube.ML

$(BIN)/Cube:   $(BIN)/Pure  $(FILES) 
	case "$(COMP)" in \
	poly*)	echo 'make_database"$(BIN)/Cube"; quit();'  \
			| $(COMP) $(BIN)/Pure;\
                if [ "$${MAKE_HTML}" = "true" ]; \
                then echo 'open PolyML; make_html := true; exit_use_dir".";' \
                       | $(COMP) $(BIN)/Cube;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
                then echo 'open PolyML; make_html := true; exit_use_dir".";                               make_html := false;' | $(COMP) $(BIN)/Cube;\
                else echo 'open PolyML; exit_use_dir".";' \
		       | $(COMP) $(BIN)/Cube;\
                fi;\
		discgarb -c $(BIN)/Cube;;\
	sml*)	if [ "$${MAKE_HTML}" = "true" ]; \
                then echo 'make_html := true; exit_use_dir".";                                            xML"$(BIN)/Cube" banner;' | $(BIN)/Pure;\
                elif [ "$${MAKE_HTML-undefined}" != "undefined" ];\
                then echo 'make_html := true; exit_use_dir".";                                            make_html := false; xML"$(BIN)/Cube" banner;' \
                       | $(BIN)/Pure;\
                else echo 'exit_use_dir"."; xML"$(BIN)/Cube" banner;' \
                       | $(BIN)/Pure;\
                fi;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

$(BIN)/Pure:
	cd ../Pure;  $(MAKE)

test:   ex.ML $(BIN)/Cube
	case "$(COMP)" in \
	poly*)	echo 'exit_use"ex.ML"; quit();' | $(COMP) $(BIN)/Cube ;;\
	sml*)	echo 'exit_use"ex.ML";' | $(BIN)/Cube;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:  $(BIN)/Pure  $(BIN)/Cube 
