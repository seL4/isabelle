#  $Id$
#########################################################################
#									#
#	Makefile for the report "Isabelle's Object-Logics"		#
#									#
#########################################################################


FILES =  logics.tex preface.tex syntax.tex LK.tex CTT.tex\
	 ../rail.sty ../proof.sty ../iman.sty ../extra.sty

logics.dvi.gz:   $(FILES) 
	test -r isabelle.eps || ln -s ../gfx/isabelle.eps .
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
	test -r isabelle.eps || ln -s ../gfx/isabelle.eps .
	-rm logics.dvi*
	latex logics
	latex logics
	../sedindex logics
	latex logics

clean:
	@rm *.aux *.log *.toc *.idx *.rai

