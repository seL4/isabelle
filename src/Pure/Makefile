#  $Id$
#########################################################################
#									#
#			Makefile for Isabelle (Pure)			#
#									#
#########################################################################

#The pure part is common to all systems.  
#Object-logics (like FOL) are loaded on top of it.

#To make the system, cd to this directory and type  
#	make -f Makefile 

#Environment variable ML_DBASE specifies the initial Poly/ML database, from
#  the Poly/ML distribution directory.
#WARNING: Poly/ML parent databases should not be moved!

#Environment variable ISABELLECOMP specifies the compiler.
#Environment variable ISABELLEBIN specifies the destination directory.
#For Poly/ML, ISABELLEBIN must begin with a /

BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)
FILES =	POLY.ML NJ.ML ROOT.ML library.ML term.ML symtab.ML type.ML sign.ML\
	sequence.ML envir.ML pattern.ML unify.ML logic.ML theory.ML thm.ML\
	net.ML display.ML deriv.ML drule.ML tctical.ML search.ML tactic.ML\
	goals.ML axclass.ML install_pp.ML\
	NJ093.ML NJ1xx.ML ../Provers/simplifier.ML

SYNTAX_FILES =	Syntax/ROOT.ML	Syntax/ast.ML		Syntax/lexicon.ML\
	Syntax/parser.ML	Syntax/type_ext.ML	Syntax/syn_trans.ML\
	Syntax/pretty.ML	Syntax/printer.ML	Syntax/syntax.ML\
	Syntax/syn_ext.ML	Syntax/mixfix.ML

THY_FILES = Thy/ROOT.ML		Thy/thy_scan.ML		Thy/thy_parse.ML\
	Thy/thy_syn.ML		Thy/thy_read.ML		Thy/thm_database.ML

#Uses cp rather than make_database because Poly/ML allows only 3 levels
$(BIN)/Pure:   $(FILES)	 $(SYNTAX_FILES)  $(THY_FILES)	$(ML_DBASE)
	@case `expr "//$(COMP)" : '[^ ]*/\(.*\)'` in \
	poly*)	echo database=$${ML_DBASE:?'No Poly/ML database specified'};\
		cp $(ML_DBASE) $(BIN)/Pure; chmod u+w $(BIN)/Pure;\
		echo 'PolyML.use"POLY";use"ROOT" handle _=> exit 1;' \
		  | $(COMP) $(BIN)/Pure;\
		discgarb -c $(BIN)/Pure;;\
	sml*)	if [ ! '(' -d $${ISABELLEBIN:?} -a -w $${ISABELLEBIN:?} ')' ];\
		then echo Bad value for ISABELLEBIN: \
			$(BIN) is not a writable directory; \
			exit 1; \
		fi;\
		echo 'use"NJ.ML"; use"ROOT.ML" handle _=> exit 1;				     xML"$(BIN)/Pure" banner;' | $(COMP);;\
	*)	echo Bad value for ISABELLECOMP: \
			\"$(COMP)\" is not poly or sml;;\
	esac


test: $(BIN)/Pure

.PRECIOUS:  $(BIN)/Pure	 
