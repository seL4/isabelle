#  $Id$
#########################################################################
#									#
#	Makefile for the report "Introduction to Isabelle"		#
#									#
#########################################################################


FILES =  intro.tex foundations.tex getting.tex advanced.tex \
	 ../proof.sty ../iman.sty ../extra.sty

intro.dvi.gz:   $(FILES)
	-rm intro.dvi*
	latex intro
	bibtex intro
	latex intro
	latex intro
	../sedindex intro
	latex intro
	gzip -f intro.dvi

dist:   $(FILES)
	-rm intro.dvi*
	latex intro
	latex intro
	../sedindex intro
	latex intro

clean:
	@rm *.aux *.log *.toc *.idx
