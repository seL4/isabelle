# $Id$
#########################################################################
#									#
# 			Makefile for Isabelle (HOL)			#
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
       mono Lfp Gfp Nat Inductive Finite Arith Sexp Univ List RelPow

FILES = ROOT.ML add_ind_def.ML datatype.ML hologic.ML\
	ind_syntax.ML indrule.ML intr_elim.ML simpdata.ML\
	typedef.ML thy_syntax.ML ../Pure/section_utils.ML\
	../Provers/hypsubst.ML ../Provers/classical.ML\
        ../Provers/simplifier.ML ../Provers/splitter.ML\
 	$(NAMES:%=%.thy) $(NAMES:%=%.ML)

$(BIN)/HOL:   $(BIN)/Pure  $(FILES) 
	if [ -d $${ISABELLEBIN:?}/Pure ];\
           	then echo Bad value for ISABELLEBIN: \
                	$(BIN) is the Isabelle source directory; \
                	exit 1; \
           	fi;\
	case "$(COMP)" in \
	poly*)	echo 'make_database"$(BIN)/HOL"; quit();'  \
		  | $(COMP) $(BIN)/Pure;\
                if [ "$${MAKE_HTML}" = "true" ]; \
                then echo 'open PolyML; make_html := true; exit_use_dir".";' \
                       | $(COMP) $(BIN)/HOL;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
                then echo 'open PolyML; make_html := true; exit_use_dir".";                               make_html := false;' | $(COMP) $(BIN)/HOL;\
                else echo 'open PolyML; exit_use_dir".";' \
                       | $(COMP) $(BIN)/HOL;\
                fi;;\
	sml*)	if [ "$${MAKE_HTML}" = "true" ]; \
                then echo 'make_html := true; exit_use_dir".";                                            xML"$(BIN)/HOL" banner;' | $(BIN)/Pure;\
                elif [ "$${MAKE_HTML-undefined}" != "undefined" ];\
                then echo 'make_html := true; exit_use_dir".";                                            make_html := false; xML"$(BIN)/HOL" banner;' \
                       | $(BIN)/Pure;\
                else echo 'exit_use_dir"."; xML"$(BIN)/HOL" banner;' \
                       | $(BIN)/Pure;\
                fi;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml; exit 1;;\
	esac

$(BIN)/Pure:
	cd ../Pure;  $(MAKE)

#### Testing of HOL

#A macro referring to the object-logic (depends on ML compiler)
LOGIC:sh=case $ISABELLECOMP in \
	poly*)	echo "$ISABELLECOMP $ISABELLEBIN/HOL" ;;\
	sml*)	echo "$ISABELLEBIN/HOL" ;;\
	*)	echo "echo Bad value for ISABELLECOMP: \
                	$ISABELLEBIN is not poly or sml; exit 1" ;;\
	esac

##IMP-semantics example
IMP_NAMES = Com Denotation Equiv Properties
IMP_FILES = IMP/ROOT.ML $(IMP_NAMES:%=IMP/%.thy) $(IMP_NAMES:%=IMP/%.ML)

IMP:    $(BIN)/HOL  $(IMP_FILES)
	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
        then echo 'make_html := true; exit_use_dir"IMP";quit();' | $(LOGIC); \
        else echo 'exit_use_dir"IMP";quit();' | $(LOGIC); \
        fi

##Hoare logic
Hoare_NAMES = Hoare Arith2 Examples
Hoare_FILES = Hoare/ROOT.ML $(Hoare_NAMES:%=Hoare/%.thy) \
              $(Hoare_NAMES:%=Hoare/%.ML)

Hoare:  $(BIN)/HOL  $(Hoare_FILES)
	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
        then echo 'make_html := true; exit_use_dir"Hoare";quit();' | $(LOGIC);\
        else echo 'exit_use_dir"Hoare";quit();' | $(LOGIC); \
        fi

##The integers in HOL
INTEG_NAMES = Equiv Integ 

INTEG_FILES = Integ/ROOT.ML \
              $(INTEG_NAMES:%=Integ/%.thy) $(INTEG_NAMES:%=Integ/%.ML)

Integ:  $(BIN)/HOL  $(INTEG_FILES)
	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
        then echo 'make_html := true; exit_use_dir"Integ";quit();' | $(LOGIC);\
        else echo 'exit_use_dir"Integ";quit();' | $(LOGIC); \
        fi

##I/O Automata
IOA_NTP_NAMES = Abschannel Action Correctness Impl Lemmas Multiset Packet\
                Receiver Sender
IOA_ABP_NAMES = Action Correctness Lemmas
IOA_MT_NAMES = Asig IOA Option Solve

IOA_FILES = IOA/NTP/ROOT.ML IOA/ABP/ROOT.ML IOA/NTP/Spec.thy\
 $(IOA_NTP_NAMES:%=IOA/NTP/%.thy) $(IOA_NTP_NAMES:%=IOA/NTP/%.ML)\
 IOA/ABP/Abschannel.thy IOA/ABP/Abschannel_finite.thy IOA/ABP/Env.thy\
 IOA/ABP/Impl.thy IOA/ABP/Impl_finite.thy IOA/ABP/Packet.thy\
 IOA/ABP/Receiver.thy IOA/ABP/Sender.thy IOA/ABP/Spec.thy\
 $(IOA_ABP_NAMES:%=IOA/ABP/%.thy) $(IOA_ABP_NAMES:%=IOA/ABP/%.ML)\
 $(IOA_MT_NAMES:%=IOA/meta_theory/%.thy) $(IOA_MT_NAMES:%=IOA/meta_theory/%.ML)

IOA:    $(BIN)/HOL  $(IOA_FILES)
	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
        then echo 'make_html := true; exit_use_dir"IOA/NTP";quit();' \
               | $(LOGIC);\
             echo 'make_html := true; exit_use_dir"IOA/ABP";quit();' \
               | $(LOGIC);\
        else echo 'exit_use_dir"IOA/NTP";quit();' | $(LOGIC); \
	     echo 'exit_use_dir"IOA/ABP";quit();' | $(LOGIC); \
        fi

##Properties of substitutions
SUBST_NAMES = AList Setplus Subst Unifier UTerm UTLemmas

SUBST_FILES = Subst/ROOT.ML \
              $(SUBST_NAMES:%=Subst/%.thy) $(SUBST_NAMES:%=Subst/%.ML)

Subst:  $(BIN)/HOL  $(SUBST_FILES)
	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
        then echo 'make_html := true; exit_use_dir"Subst";quit();' | $(LOGIC);\
        else echo 'exit_use_dir"Subst";quit();' | $(LOGIC); \
        fi

##Confluence of Lambda-calculus
LAMBDA_NAMES = Lambda ParRed Commutation Eta

LAMBDA_FILES = Lambda/ROOT.ML \
              $(LAMBDA_NAMES:%=Lambda/%.thy) $(LAMBDA_NAMES:%=Lambda/%.ML)

Lambda:  $(BIN)/HOL $(LAMBDA_FILES)
	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
        then echo 'make_html := true; exit_use_dir"Lambda";quit();' \
               | $(LOGIC);\
        else echo 'exit_use_dir"Lambda";quit();' | $(LOGIC); \
        fi

##Type inference for MiniML
MINIML_NAMES = I Maybe MiniML Type W

MINIML_FILES = MiniML/ROOT.ML \
              $(MINIML_NAMES:%=MiniML/%.thy) $(MINIML_NAMES:%=MiniML/%.ML)

MiniML: $(BIN)/HOL  $(MINIML_FILES)
	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
        then echo 'make_html := true; exit_use_dir"MiniML";quit();' \
               | $(LOGIC);\
        else echo 'exit_use_dir"MiniML";quit();' | $(LOGIC); \
        fi

##Lexical analysis
LEX_FILES = Auto AutoChopper Chopper Prefix

LEX_FILES = Lex/ROOT.ML \
            $(LEX_NAMES:%=Lex/%.thy) $(LEX_NAMES:%=Lex/%.ML)

Lex:	$(BIN)/HOL  $(LEX_FILES)
	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
        then echo 'make_html := true; exit_use_dir"Lex";quit();' | $(LOGIC);\
        else echo 'exit_use_dir"Lex";quit();' | $(LOGIC); \
        fi

##Miscellaneous examples
EX_NAMES = LexProd MT Acc PropLog Puzzle Qsort LList Rec Simult Term String \
	   BT Perm

EX_FILES = ex/ROOT.ML ex/cla.ML ex/meson.ML ex/mesontest.ML ex/rel.ML \
           ex/set.ML $(EX_NAMES:%=ex/%.thy) $(EX_NAMES:%=ex/%.ML)

ex:     $(BIN)/HOL  $(EX_FILES)
	if [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
        then echo 'make_html := true; exit_use_dir"ex";quit();' | $(LOGIC);\
        else echo 'exit_use_dir"ex";quit();' | $(LOGIC); \
        fi

#Full test.
test:   $(BIN)/HOL IMP Hoare Lex Integ Subst Lambda MiniML IOA ex
	echo 'Test examples ran successfully' > test

.PRECIOUS:  $(BIN)/Pure $(BIN)/HOL 
