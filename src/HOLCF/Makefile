# $Id$
############################################################################
#									   #
#		    Makefile for Isabelle (HOLCF)			   #
#									   #
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
THYS = Porder.thy Porder0.thy Pcpo.thy \
       Fun1.thy Fun2.thy Fun3.thy \
       Cfun1.thy Cfun2.thy Cfun3.thy Cont.thy \
       Cprod1.thy Cprod2.thy Cprod3.thy \
       Sprod0.thy Sprod1.thy Sprod2.thy Sprod3.thy \
       Ssum0.thy Ssum1.thy Ssum2.thy Ssum3.thy \
       Up1.thy Up2.thy Up3.thy Fix.thy ccc1.thy \
       One.thy Tr.thy \
       Lift1.thy Lift2.thy Lift3.thy HOLCF.thy 

ONLYTHYS = Lift.thy

FILES = ROOT.ML $(THYS) $(ONLYTHYS) $(THYS:.thy=.ML) \
        ax_ops/holcflogic.ML ax_ops/thy_axioms.ML \
        ax_ops/thy_ops.ML    ax_ops/thy_syntax.ML \
        domain/library.ML  domain/syntax.ML   domain/axioms.ML \
        domain/theorems.ML domain/extender.ML domain/interface.ML

#Uses cp rather than make_database because Poly/ML allows only 3 levels
$(BIN)/HOLCF:	$(BIN)/HOL  $(FILES) 
	@case `basename "$(COMP)"` in \
	poly*)	cp $(BIN)/HOL $(BIN)/HOLCF; chmod u+w $(BIN)/HOLCF;\
		if [ "$${MAKE_HTML}" = "true" ]; \
		then echo 'open PolyML; make_html := true; exit_use_dir".";' \
		       | $(COMP) $(BIN)/HOLCF;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
		then echo 'open PolyML; make_html := true; exit_use_dir".";				  make_html := false;' | $(COMP) $(BIN)/HOLCF;\
		else echo 'open PolyML; exit_use_dir".";' \
		       | $(COMP) $(BIN)/HOLCF;\
		fi;\
		discgarb -c $(BIN)/HOLCF;;\
	sml*)	if [ "$${MAKE_HTML}" = "true" ]; \
		then echo 'make_html := true; exit_use_dir".";						  xML"$(BIN)/HOLCF" banner;' | $(BIN)/HOL;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ];\
		then echo 'make_html := true; exit_use_dir".";						  make_html := false; xML"$(BIN)/HOLCF" banner;' \
		       | $(BIN)/HOL;\
		else echo 'exit_use_dir"."; xML"$(BIN)/HOLCF" banner;' \
		       | $(BIN)/HOL;\
		fi;;\
	*)	echo Bad value for ISABELLECOMP: \
			\"$(COMP)\" is not poly or sml;;\
	esac

$(BIN)/HOL:
	cd ../HOL;  $(MAKE)

EX_THYS = ex/Classlib.thy\
	  ex/Dnat.thy ex/Dlist.thy ex/Stream.thy\
	  ex/Dagstuhl.thy ex/Focus_ex.thy ex/Fix2.thy\
	  ex/Hoare.thy ex/Loop.thy

EX_FILES = ex/ROOT.ML ex/loeckx.ML $(EX_THYS) $(EX_THYS:.thy=.ML)

test:	ex/ROOT.ML  $(BIN)/HOLCF  $(EX_FILES) 
	@case `basename "$(COMP)"` in \
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
			\"$(COMP)\" is not poly or sml;;\
	esac

.PRECIOUS:  $(BIN)/HOL	$(BIN)/HOLCF 

