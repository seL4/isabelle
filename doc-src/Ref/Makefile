#  $Id$
#########################################################################
#									#
#	Makefile for the report "The Isabelle Reference Manual"		#
#									#
#########################################################################


FILES =  ref.tex introduction.tex goals.tex tactic.tex tctical.tex\
         thm.tex theories.tex defining.tex syntax.tex substitution.tex\
         simplifier.tex classical.tex theory-syntax.tex\
	 ../rail.sty ../proof.sty ../iman.sty ../extra.sty

ref.dvi.gz:   $(FILES) 
	-rm ref.dvi*
	latex ref
	rail ref
	bibtex ref
	latex ref
	latex ref
	../sedindex ref
	latex ref
	gzip -f ref.dvi

dist:   $(FILES) 
	-rm ref.dvi*
	latex ref
	latex ref
	../sedindex ref
	latex ref
