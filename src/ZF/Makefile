#########################################################################
#									#
# 			Makefile for Isabelle (ZF)			#
#									#
#########################################################################

#To make the system, cd to this directory and type
#	make -f Makefile 
#To make the system and test it on standard examples, type 
#	make -f Makefile test

#Environment variable ISABELLECOMP specifies the compiler.
#Environment variable ISABELLEBIN specifies the destination directory.
#For Poly/ML, ISABELLEBIN must begin with a /

#Makes FOL if this file is ABSENT -- but not 
#if it is out of date, since this Makefile does not know its dependencies!

BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)
FILES = ROOT.ML zf.thy zf.ML upair.ML subset.ML pair.ML domrange.ML \
	func.ML simpdata.ML bool.thy bool.ML \
	sum.thy sum.ML qpair.thy qpair.ML mono.ML fixedpt.thy fixedpt.ML \
	ind_syntax.ML intr_elim.ML indrule.ML inductive.ML coinductive.ML \
	equalities.ML perm.thy perm.ML trancl.thy trancl.ML \
	wf.thy wf.ML ord.thy ord.ML nat.thy nat.ML \
	epsilon.thy epsilon.ML arith.thy arith.ML univ.thy univ.ML \
	quniv.thy quniv.ML constructor.ML datatype.ML  \
	fin.ML list.ML listfn.thy listfn.ML

#Uses cp rather than make_database because Poly/ML allows only 3 levels
$(BIN)/ZF:   $(BIN)/FOL  $(FILES) 
	case "$(COMP)" in \
	poly*)	cp $(BIN)/FOL $(BIN)/ZF;\
		echo 'open PolyML; use"ROOT";' | $(COMP) $(BIN)/ZF ;;\
	sml*)	echo 'use"ROOT.ML"; xML"$(BIN)/ZF" banner;' | $(BIN)/FOL;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

$(BIN)/FOL:
	cd ../FOL;  $(MAKE)

test:   ex/ROOT.ML  $(BIN)/ZF
	case "$(COMP)" in \
	poly*)	echo 'use"ex/ROOT.ML"; quit();' | $(COMP) $(BIN)/ZF ;;\
	sml*)	echo 'use"ex/ROOT.ML";' | $(BIN)/ZF;;\
	*)	echo Bad value for ISABELLECOMP;;\
	esac

.PRECIOUS:  $(BIN)/FOL $(BIN)/ZF 
