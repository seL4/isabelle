# $Id$
#########################################################################
#									#
#			Makefile for Isabelle (HOL)			#
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
NAMES = HOL Ord Set Fun subset equalities Prod Relation Trancl Sum WF \
	mono Lfp Gfp Nat intr_elim indrule Inductive Finite Arith \
	Sexp Univ List RelPow Option

FILES = ROOT.ML add_ind_def.ML datatype.ML hologic.ML\
	ind_syntax.ML cladata.ML simpdata.ML\
	typedef.ML thy_syntax.ML thy_data.ML ../Pure/section_utils.ML\
	../Provers/hypsubst.ML ../Provers/classical.ML\
	../Provers/simplifier.ML ../Provers/splitter.ML\
	$(NAMES:%=%.thy) $(NAMES:%=%.ML)

$(BIN)/HOL:   $(BIN)/Pure  $(FILES) 
	@if [ -d $${ISABELLEBIN:?}/Pure ];\
		then echo Bad value for ISABELLEBIN: \
			$(BIN) is the Isabelle source directory; \
			exit 1; \
	fi
	@case `basename "$(COMP)"` in \
	poly*)	echo 'make_database"$(BIN)/HOL"; quit();'  \
		  | $(COMP) $(BIN)/Pure;\
		if [ "$${MAKE_HTML}" = "true" ]; \
		then echo 'open PolyML; make_html := true; exit_use_dir".";' \
		       | $(COMP) $(BIN)/HOL;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
		then echo 'open PolyML; make_html := true; exit_use_dir".";				  make_html := false;' | $(COMP) $(BIN)/HOL;\
		else echo 'open PolyML; exit_use_dir".";' \
		       | $(COMP) $(BIN)/HOL;\
		fi;\
		discgarb -c $(BIN)/HOL;;\
	sml*)	if [ "$${MAKE_HTML}" = "true" ]; \
		then echo 'make_html := true; exit_use_dir".";						  xML"$(BIN)/HOL" banner;' | $(BIN)/Pure;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ];\
		then echo 'make_html := true; exit_use_dir".";						  make_html := false; xML"$(BIN)/HOL" banner;' \
		       | $(BIN)/Pure;\
		else echo 'exit_use_dir"."; xML"$(BIN)/HOL" banner;' \
		       | $(BIN)/Pure;\
		fi;;\
	*)	echo Bad value for ISABELLECOMP: \
			\"$(COMP)\" is not poly or sml; exit 1;;\
	esac

$(BIN)/Pure:
	cd ../Pure;  $(MAKE)

#### Testing of HOL

#A macro referring to the object-logic (depends on ML compiler)
#	[Thanks to Thomas Santen and Stephan Herrmann from GMD First]
LOGIC=`case \`basename "$(ISABELLECOMP)"\` in \
	poly*)	echo "$(ISABELLECOMP) $(ISABELLEBIN)/HOL" ;;\
	sml*)	echo "$(ISABELLEBIN)/HOL" ;;\
	*)	echo "echo; echo Bad value for ISABELLECOMP: \
			$(ISABELLECOMP) is not poly or sml; exit 1" ;;\
	esac`

##TFL (requires integration into HOL proper)
TFL_NAMES = mask tfl thms thry usyntax utils
TFL_FILES = ../TFL/ROOT.ML ../TFL/sys.sml \
            $(TFL_NAMES:%=../TFL/%.sig) $(TFL_NAMES:%=../TFL/%.sml)

TFL:	$(BIN)/HOL  $(TFL_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html:= true; exit_use_dir"../TFL";quit();' | $(LOGIC);\
	else echo 'exit_use_dir"../TFL";quit();' | $(LOGIC); \
	fi

##IMP-semantics example
IMP_NAMES = Expr Com Natural Transition Denotation Hoare VC
IMP_FILES = IMP/ROOT.ML $(IMP_NAMES:%=IMP/%.thy) $(IMP_NAMES:%=IMP/%.ML)

IMP:	$(BIN)/HOL  $(IMP_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"IMP";quit();' | $(LOGIC); \
	else echo 'exit_use_dir"IMP";quit();' | $(LOGIC); \
	fi

##Hoare logic
Hoare_NAMES = Hoare Arith2 Examples
Hoare_FILES = Hoare/ROOT.ML $(Hoare_NAMES:%=Hoare/%.thy) \
	      $(Hoare_NAMES:%=Hoare/%.ML)

Hoare:	$(BIN)/HOL  $(Hoare_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"Hoare";quit();' | $(LOGIC);\
	else echo 'exit_use_dir"Hoare";quit();' | $(LOGIC); \
	fi

##The integers in HOL
INTEG_NAMES = Equiv Integ Group Ring Lagrange IntRingDefs IntRing

INTEG_FILES = Integ/ROOT.ML \
	      $(INTEG_NAMES:%=Integ/%.thy) $(INTEG_NAMES:%=Integ/%.ML)

Integ:	$(BIN)/HOL  $(INTEG_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"Integ";quit();' | $(LOGIC);\
	else echo 'exit_use_dir"Integ";quit();' | $(LOGIC); \
	fi

##I/O Automata
IOA_NTP_NAMES = Abschannel Action Correctness Impl Lemmas Multiset Packet\
		Receiver Sender
IOA_ABP_NAMES = Action Correctness Lemmas
IOA_MT_NAMES = Asig IOA Solve

IOA_FILES = IOA/NTP/ROOT.ML IOA/ABP/ROOT.ML IOA/NTP/Spec.thy\
 $(IOA_NTP_NAMES:%=IOA/NTP/%.thy) $(IOA_NTP_NAMES:%=IOA/NTP/%.ML)\
 IOA/ABP/Abschannel.thy IOA/ABP/Abschannel_finite.thy IOA/ABP/Env.thy\
 IOA/ABP/Impl.thy IOA/ABP/Impl_finite.thy IOA/ABP/Packet.thy\
 IOA/ABP/Receiver.thy IOA/ABP/Sender.thy IOA/ABP/Spec.thy\
 $(IOA_ABP_NAMES:%=IOA/ABP/%.thy) $(IOA_ABP_NAMES:%=IOA/ABP/%.ML)\
 $(IOA_MT_NAMES:%=IOA/meta_theory/%.thy) $(IOA_MT_NAMES:%=IOA/meta_theory/%.ML)

IOA:	$(BIN)/HOL  $(IOA_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"IOA/NTP";quit();' \
	       | $(LOGIC);\
	     echo 'make_html := true; exit_use_dir"IOA/ABP";quit();' \
	       | $(LOGIC);\
	else echo 'exit_use_dir"IOA/NTP";quit();' | $(LOGIC); \
	     echo 'exit_use_dir"IOA/ABP";quit();' | $(LOGIC); \
	fi


##Authentication & Security Protocols
Auth_NAMES = Message Shared NS_Shared OtwayRees OtwayRees_AN OtwayRees_Bad \
	     Recur WooLam Yahalom Yahalom2 Public NS_Public_Bad NS_Public

AUTH_FILES = Auth/ROOT.ML $(AUTH_NAMES:%=Auth/%.thy) $(AUTH_NAMES:%=Auth/%.ML)

Auth:	$(BIN)/HOL  $(AUTH_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"Auth";quit();' | $(LOGIC);\
	else echo 'exit_use_dir"Auth";quit();' | $(LOGIC); \
	fi


##Properties of substitutions
SUBST_NAMES = AList Setplus Subst Unifier UTerm UTLemmas

SUBST_FILES = Subst/ROOT.ML \
	      $(SUBST_NAMES:%=Subst/%.thy) $(SUBST_NAMES:%=Subst/%.ML)

Subst:	$(BIN)/HOL  $(SUBST_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"Subst";quit();' | $(LOGIC);\
	else echo 'exit_use_dir"Subst";quit();' | $(LOGIC); \
	fi

##Confluence of Lambda-calculus
LAMBDA_NAMES = Lambda ParRed Commutation Eta

LAMBDA_FILES = Lambda/ROOT.ML \
	      $(LAMBDA_NAMES:%=Lambda/%.thy) $(LAMBDA_NAMES:%=Lambda/%.ML)

Lambda:	 $(BIN)/HOL $(LAMBDA_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"Lambda";quit();' \
	       | $(LOGIC);\
	else echo 'exit_use_dir"Lambda";quit();' | $(LOGIC); \
	fi

## Type inference without let

W0_NAMES = I Maybe MiniML Type W

W0_FILES = W0/ROOT.ML \
	      $(W0_NAMES:%=W0/%.thy) $(W0_NAMES:%=W0/%.ML)

W0:	$(BIN)/HOL  $(W0_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"W0";quit();' \
	       | $(LOGIC);\
	else echo 'exit_use_dir"W0";quit();' | $(LOGIC); \
	fi

## Type inference with let

MINIML_NAMES = Generalize Instance Maybe MiniML Type W

MINIML_FILES = MiniML/ROOT.ML \
	      $(MINIML_NAMES:%=MiniML/%.thy) $(MINIML_NAMES:%=MiniML/%.ML)

MiniML: $(BIN)/HOL  $(MINIML_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"MiniML";quit();' \
	       | $(LOGIC);\
	else echo 'exit_use_dir"MiniML";quit();' | $(LOGIC); \
	fi

##Lexical analysis
LEX_FILES = Auto AutoChopper Chopper Prefix

LEX_FILES = Lex/ROOT.ML \
	    $(LEX_NAMES:%=Lex/%.thy) $(LEX_NAMES:%=Lex/%.ML)

Lex:	$(BIN)/HOL  $(LEX_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"Lex";quit();' | $(LOGIC);\
	else echo 'exit_use_dir"Lex";quit();' | $(LOGIC); \
	fi

##Miscellaneous examples
EX_NAMES = String BT Perm Comb InSort Qsort LexProd \
	   Puzzle Mutil Primes NatSum SList LList Acc PropLog Term Simult MT

EX_FILES = ex/ROOT.ML ex/cla.ML ex/meson.ML ex/mesontest.ML ex/rel.ML \
	   ex/set.ML $(EX_NAMES:%=ex/%.thy) $(EX_NAMES:%=ex/%.ML)

ex:	$(BIN)/HOL  $(EX_FILES)
	@if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
	then echo 'make_html := true; exit_use_dir"ex";quit();' | $(LOGIC);\
	else echo 'exit_use_dir"ex";quit();' | $(LOGIC); \
	fi

#Full test.
test:	$(BIN)/HOL TFL IMP Hoare Lex Integ Auth Subst Lambda MiniML IOA ex
	echo 'Test examples ran successfully' > test

.PRECIOUS:  $(BIN)/Pure $(BIN)/HOL 
