#  $Id$
#########################################################################
#									#
#	Makefile for the report "Isabelle/HOL. The Tutorial"		#
#									#
#########################################################################


FILES =  tutorial.tex basics.tex fp.tex appendix.tex \
	 ../iman.sty ttbox.sty extra.sty

tutorial.ps.gz:   $(FILES)
	isatool make
	-ln -sf ../gfx/isabelle_hol.eps .
	-rm tutorial.dvi*
	latex tutorial
	bibtex tutorial
	latex tutorial
	latex tutorial
	../sedindex tutorial
	latex tutorial
	dvips tutorial.dvi -o tutorial.ps
	gzip tutorial.ps

dist:   $(FILES) 
	-ln -sf ../gfx/isabelle_hol.eps .
	-rm tutorial.dvi*
	latex tutorial
	latex tutorial
	../sedindex tutorial
	latex tutorial

clean:
	@rm *.aux *.log *.toc *.idx
