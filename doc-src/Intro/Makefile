#  $Id$
#########################################################################
#									#
#	Makefile for the report "Introduction to Isabelle"		#
#									#
#########################################################################


FILES =  intro.tex foundations.tex getting.tex advanced.tex \
	 ../proof209.sty ../iman.sty ../extra.sty

intro.dvi:   $(FILES) 
	-rm intro.dvi*
	latex209 intro
	-test -f string.bib && bibtex intro
	latex209 intro
	latex209 intro
	../sedindex intro
	latex209 intro

intro.dvi.gz: intro.dvi
	gzip -f intro.dvi
