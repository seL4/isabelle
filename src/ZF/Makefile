# $Id$
#########################################################################
#									#
#			Makefile for Isabelle (ZF)			#
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
NAMES = ZF upair subset pair domrange \
	func AC simpdata equalities Bool \
	Sum QPair mono Fixedpt ind_syntax cartprod add_ind_def \
	constructor intr_elim indrule Inductive Perm Rel EquivClass Trancl \
	WF Order Ordinal Epsilon Arith Univ \
	QUniv Datatype OrderArith OrderType \
	Cardinal CardinalArith Cardinal_AC InfDatatype \
	Zorn Nat Finite List 

FILES = ROOT.ML thy_syntax.ML ../Pure/section_utils.ML \
	$(NAMES:%=%.thy) $(NAMES:%=%.ML)

#Uses cp rather than make_database because Poly/ML allows only 3 levels
$(BIN)/ZF:   $(BIN)/FOL	 $(FILES) 
	@case `basename "$(COMP)"` in \
	poly*)	cp $(BIN)/FOL $(BIN)/ZF;\
		if [ "$${MAKE_HTML}" = "true" ]; \
		then echo 'open PolyML; make_html := true; exit_use_dir".";' \
		       | $(COMP) $(BIN)/ZF;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
		then echo 'open PolyML; make_html := true; exit_use_dir".";				  make_html := false;' | $(COMP) $(BIN)/ZF;\
		else echo 'open PolyML; exit_use_dir".";' \
		       | $(COMP) $(BIN)/ZF;\
		fi;\
		discgarb -c $(BIN)/ZF;;\
	sml*)	if [ "$${MAKE_HTML}" = "true" ]; \
		then echo 'make_html := true; exit_use_dir".";						  xML"$(BIN)/ZF" banner;' | $(BIN)/FOL;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ];\
		then echo 'make_html := true; exit_use_dir".";						  make_html := false; xML"$(BIN)/ZF" banner;' \
		       | $(BIN)/FOL;\
		else echo 'exit_use_dir"."; xML"$(BIN)/ZF" banner;' \
		       | $(BIN)/FOL;\
		fi;;\
	*)	echo Bad value for ISABELLECOMP: \
			\"$(COMP)\" is not poly or sml; exit 1;;\
	esac

$(BIN)/FOL:
	cd ../FOL;  $(MAKE)

#### Testing of ZF

#A macro referring to the object-logic (depends on ML compiler)
#	[Thanks to Thomas Santen and Stephan Herrmann from GMD First]
LOGIC=`case \`basename "$(ISABELLECOMP)"\` in \
	poly*)	echo "$(ISABELLECOMP) $(ISABELLEBIN)/ZF" ;;\
	sml*)	echo "$(ISABELLEBIN)/ZF" ;;\
	*)	echo "echo; echo Bad value for ISABELLECOMP: \
			$(ISABELLECOMP) is not poly or sml; exit 1" ;;\
	esac`

##IMP-semantics example
IMP_NAMES = Com Denotation Equiv
IMP_FILES = IMP/ROOT.ML $(IMP_NAMES:%=IMP/%.thy) $(IMP_NAMES:%=IMP/%.ML)

IMP:   $(BIN)/ZF  $(IMP_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"IMP";quit();' | $(LOGIC); \
	else echo 'exit_use_dir"IMP";quit();' | $(LOGIC); \
	fi

##Coinduction example
COIND_NAMES = ECR Language MT Map Static Types Values 

COIND_FILES = Coind/ROOT.ML Coind/BCR.thy  Coind/Dynamic.thy \
	      $(COIND_NAMES:%=Coind/%.thy) $(COIND_NAMES:%=Coind/%.ML)

Coind:	$(BIN)/ZF  $(COIND_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"Coind";quit();' | $(LOGIC);\
	else echo 'exit_use_dir"Coind";quit();' | $(LOGIC); \
	fi

##AC examples
AC_NAMES = AC_Equiv OrdQuant Transrec2 Cardinal_aux \
	   AC15_WO6 AC16_WO4 AC16_lemmas AC17_AC1 AC18_AC19 AC1_WO2 \
	   DC DC_lemmas HH Hartog WO1_AC \
	   WO2_AC16 WO6_WO1 WO_AC first recfunAC16 rel_is_fun

AC_FILES = AC/ROOT.ML AC/AC0_AC1.ML AC/AC10_AC15.ML AC/AC1_AC17.ML \
	   AC/AC2_AC6.ML AC/AC7_AC9.ML \
	   AC/WO1_WO6.ML AC/WO1_WO7.ML AC/WO1_WO8.ML \
	   $(AC_NAMES:%=AC/%.thy) $(AC_NAMES:%=AC/%.ML)

AC:  $(BIN)/ZF	$(AC_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"AC";quit();' | $(LOGIC); \
	else echo 'exit_use_dir"AC";quit();' | $(LOGIC); \
	fi

##Residuals example

RESID_NAMES = Confluence Redex SubUnion Conversion Reduction Substitution \
	      Cube Residuals Terms

RESID_FILES = Resid/ROOT.ML $(RESID_NAMES:%=Resid/%.thy) \
			    $(RESID_NAMES:%=Resid/%.ML)

Resid:	$(BIN)/ZF  $(RESID_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"Resid";quit();' | $(LOGIC);\
	else echo 'exit_use_dir"Resid";quit();' | $(LOGIC); \
	fi

##Miscellaneous examples
EX_NAMES = Primes Ramsey Limit Integ twos_compl Bin BT Term TF Ntree Brouwer \
	   Data Enum Rmap Mutil PropLog ListN Acc Comb Primrec LList CoUnit 

EX_FILES = ex/ROOT.ML ex/misc.ML $(EX_NAMES:%=ex/%.thy) $(EX_NAMES:%=ex/%.ML)

#Test ZF by loading the examples in directory ex
ex:	$(BIN)/ZF  $(EX_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"ex";quit();' | $(LOGIC); \
	else echo 'exit_use_dir"ex";quit();' | $(LOGIC); \
	fi

#Full test.
test:	$(BIN)/ZF IMP Coind AC Resid ex
	echo 'Test examples ran successfully' > test

.PRECIOUS:  $(BIN)/FOL $(BIN)/ZF 
