#  $Id$
#########################################################################
#									#
#	Makefile for the report "Isabelle's Object-Logics"		#
#									#
#########################################################################


FILES =  logics.tex intro.tex FOL.tex ZF.tex HOL.tex LK.tex CTT.tex\
	 ../rail.sty ../proof.sty ../iman.sty ../extra.sty

logics.dvi.gz:   $(FILES) 
	-rm logics.dvi*
	latex logics
	rail logics
	bibtex logics
	latex logics
	latex logics
	../sedindex logics
	latex logics
	gzip -f logics.dvi

dist:   $(FILES) 
	-rm logics.dvi*
	latex logics
	latex logics
	../sedindex logics
	latex logics

clean:
	@rm *.aux *.log *.toc *.idx *.rai

