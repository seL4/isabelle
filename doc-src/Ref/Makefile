#  $Id$
#########################################################################
#									#
#	Makefile for the report "The Isabelle Reference Manual"		#
#									#
#########################################################################


FILES =  ref.tex introduction.tex goals.tex tactic.tex tctical.tex\
         thm.tex theories.tex defining.tex syntax.tex substitution.tex\
         simplifier.tex classical.tex theory-syntax.tex\
	 ../iman.sty ../extra.sty

ref.dvi.gz:   $(FILES) 
	-rm ref.dvi.gz
	latex209 ref
	rail ref
	bibtex ref
	latex209 ref
	latex209 ref
	../sedindex ref
	latex209 ref
	gzip -f ref.dvi
