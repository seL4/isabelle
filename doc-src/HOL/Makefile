#  $Id$
#########################################################################
#									#
#	Makefile for the report "Isabelle's Logics: HOL"		#
#									#
#########################################################################


FILES =  logics-HOL.tex ../Logics/syntax.tex FOL.tex HOL.tex\
	 ../rail.sty ../proof.sty ../iman.sty ../extra.sty

logics-HOL.dvi.gz:   $(FILES) 
	test -r isabelle_hol.eps || ln -s ../gfx/isabelle_hol.eps .
	-rm logics-HOL.dvi*
	latex logics-HOL
	rail logics-HOL
	bibtex logics-HOL
	latex logics-HOL
	latex logics-HOL
	../sedindex logics-HOL
	latex logics-HOL
	gzip -f logics-HOL.dvi

dist:   $(FILES) 
	test -r isabelle_hol.eps || ln -s ../gfx/isabelle_hol.eps .
	-rm logics-HOL.dvi*
	latex logics-HOL
	latex logics-HOL
	../sedindex logics-HOL
	latex logics-HOL

clean:
	@rm *.aux *.log *.toc *.idx *.rai

