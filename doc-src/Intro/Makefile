#  $Id$
#########################################################################
#									#
#	Makefile for the report "Introduction to Isabelle"		#
#									#
#########################################################################


FILES =  intro.tex foundations.tex getting.tex advanced.tex \
	 ../iman.sty ../extra.sty

intro.dvi.gz:   $(FILES) 
	-rm intro.dvi.gz
	latex209 intro
	bibtex intro
	latex209 intro
	latex209 intro
	../sedindex intro
	latex209 intro
	gzip -f intro.dvi
