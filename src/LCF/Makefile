# $Id$
#########################################################################
#									#
# 			Makefile for Isabelle (LCF)			#
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
FILES =  ROOT.ML LCF.thy LCF.ML simpdata.ML pair.ML fix.ML

#Uses cp rather than make_database because Poly/ML allows only 3 levels
$(BIN)/LCF:   $(BIN)/FOL  $(FILES) 
	case "$(COMP)" in \
	poly*)	cp $(BIN)/FOL $(BIN)/LCF;\
                if [ "$${MAKE_HTML}" = "true" ]; \
                then echo 'open PolyML; make_html := true; exit_use_dir".";' \
                       | $(COMP) $(BIN)/LCF;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
                then echo 'open PolyML; make_html := true; exit_use_dir".";                               make_html := false;' | $(COMP) $(BIN)/LCF;\
                else echo 'open PolyML; exit_use_dir".";' \
                       | $(COMP) $(BIN)/LCF;\
                fi;\
		discgarb -c $(BIN)/LCF;;\
	sml*)	if [ "$${MAKE_HTML}" = "true" ]; \
                then echo 'make_html := true; exit_use_dir".";                                            xML"$(BIN)/LCF" banner;' | $(BIN)/FOL;\
                elif [ "$${MAKE_HTML-undefined}" != "undefined" ];\
                then echo 'make_html := true; exit_use_dir".";                                            make_html := false; xML"$(BIN)/LCF" banner;' \
                       | $(BIN)/FOL;\
                else echo 'exit_use_dir"."; xML"$(BIN)/LCF" banner;' \
                       | $(BIN)/FOL;\
                fi;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

(BIN)/FOL:
	cd ../FOL;  $(MAKE)

test:   ex.ML  $(BIN)/LCF
	case "$(COMP)" in \
	poly*)	echo 'exit_use"ex.ML"; quit();' | $(COMP) $(BIN)/LCF ;;\
	sml*)	echo 'exit_use"ex.ML";' | $(BIN)/LCF;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:   $(BIN)/FOL  $(BIN)/LCF 
