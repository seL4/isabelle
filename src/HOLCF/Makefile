# $Id$
############################################################################
#                                                                          #
#                   Makefile for Isabelle (HOLCF)                          #
#                                                                          #
############################################################################

#To make the system, cd to this directory and type  
#	make
#To make the system and test it on standard examples, type 
#	make test
#To generate HTML files for every theory, set the environment variable
#MAKE_HTML or add the parameter "MAKE_HTML=".

#Environment variable ISABELLECOMP specifies the compiler.
#Environment variable ISABELLEBIN specifies the destination directory.
#For Poly/ML, ISABELLEBIN must begin with a /

#Makes HOL Isabelle if this file is ABSENT -- but not 
#if it is out of date, since this Makefile does not know its dependencies!

BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)
THYS = Holcfb.thy Void.thy Porder.thy Pcpo.thy \
       Fun1.thy Fun2.thy Fun3.thy \
       Cfun1.thy Cfun2.thy Cfun3.thy Cont.thy \
       Cprod1.thy Cprod2.thy Cprod3.thy \
       Sprod0.thy Sprod1.thy Sprod2.thy Sprod3.thy \
       Ssum0.thy Ssum1.thy Ssum2.thy Ssum3.thy \
       Lift1.thy Lift2.thy Lift3.thy Fix.thy ccc1.thy One.thy \
       Tr1.thy Tr2.thy HOLCF.thy 

FILES = ROOT.ML Porder0.thy  $(THYS) $(THYS:.thy=.ML)

#Uses cp rather than make_database because Poly/ML allows only 3 levels
$(BIN)/HOLCF:   $(BIN)/HOL  $(FILES) 
	case "$(COMP)" in \
	poly*)  cp $(BIN)/HOL $(BIN)/HOLCF; chmod u+w $(BIN)/HOLCF;\
                if [ "$${MAKE_HTML}" = "true" ]; \
                then echo 'open PolyML; make_html := true; exit_use_dir".";' \
                       | $(COMP) $(BIN)/HOLCF;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
                then echo 'open PolyML; make_html := true; exit_use_dir".";                               make_html := false;' | $(COMP) $(BIN)/HOLCF;\
                else echo 'open PolyML; exit_use_dir".";' \
		       | $(COMP) $(BIN)/HOLCF;\
                fi;\
		discgarb -c $(BIN)/HOLCF;;\
	sml*)	if [ "$${MAKE_HTML}" = "true" ]; \
                then echo 'make_html := true; exit_use_dir".";                                            xML"$(BIN)/HOLCF" banner;' | $(BIN)/HOL;\
                elif [ "$${MAKE_HTML-undefined}" != "undefined" ];\
                then echo 'make_html := true; exit_use_dir".";                                            make_html := false; xML"$(BIN)/HOLCF" banner;' \
                       | $(BIN)/HOL;\
                else echo 'exit_use_dir"."; xML"$(BIN)/HOLCF" banner;' \
                       | $(BIN)/HOL;\
                fi;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

$(BIN)/HOL:
	cd ../HOL;  $(MAKE)

EX_THYS =  ex/Fix2.thy ex/Hoare.thy \
           ex/Loop.thy  

EX_FILES = ex/ROOT.ML ex/loeckx.ML $(EX_THYS) $(EX_THYS:.thy=.ML)

test:   ex/ROOT.ML  $(BIN)/HOLCF  $(EX_FILES) 
	case "$(COMP)" in \
	poly*)	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
                then echo 'make_html := true; exit_use_dir"ex"; quit();' \
                       | $(COMP) $(BIN)/HOLCF;\
                else echo 'exit_use_dir"ex"; quit();' | $(COMP) $(BIN)/HOLCF;\
                fi;;\
	sml*)	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
                then echo 'make_html := true; exit_use_dir"ex";' \
                       | $(BIN)/HOLCF;\
                else echo 'exit_use_dir"ex";' | $(BIN)/HOLCF;\
                fi;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

EXPLICIT_DOMAINS_THYS = explicit_domains/Coind.thy explicit_domains/Dlist.thy \
			explicit_domains/Dnat2.thy explicit_domains/Stream.thy \
			explicit_domains/Dagstuhl.thy explicit_domains/Dnat.thy\
			explicit_domains/Focus_ex.thy explicit_domains/Stream2.thy

EXPLICIT_DOMAINS_FILES = explicit_domains/ROOT.ML $(EXPLICIT_DOMAINS_THYS)\
			 $(EXPLICIT_DOMAINS_THYS:.thy=.ML)

test2:	explicit_domains/ROOT.ML  $(BIN)/HOLCF  $(EXPLICIT_DOMAINS_FILES) 
	case "$(COMP)" in \
	poly*)	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
                then echo 'make_html := true; exit_use_dir"explicit_domains";                             quit();' | $(COMP) $(BIN)/HOLCF;\
                else echo 'exit_use_dir"explicit_domains"; quit();' \
                       | $(COMP) $(BIN)/HOLCF;\
                fi;;\
	sml*)	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
                then echo 'make_html := true; exit_use_dir"exlicit_domains";' \
                       | $(BIN)/HOLCF;\
                else echo 'exit_use_dir"explicit_domains";' | $(BIN)/HOLCF;\
                fi;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml;;\
	esac

.PRECIOUS:  $(BIN)/HOL  $(BIN)/HOLCF 

