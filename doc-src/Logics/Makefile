#  $Id$
#########################################################################
#									#
#	Makefile for the report "Isabelle's Object-Logics"		#
#									#
#########################################################################


FILES =  logics.tex intro.tex FOL.tex ZF.tex HOL.tex LK.tex CTT.tex\
	 ../iman.sty ../extra.sty

logics.dvi.gz:   $(FILES) 
	-rm logics.dvi.gz
	latex209 logics
	rail logics
	bibtex logics
	latex209 logics
	latex209 logics
	../sedindex logics
	latex209 logics
	gzip -f logics.dvi
