#  $Id$
#########################################################################
#									#
#	Makefile for the report "Isabelle's Logics: FOL and ZF"		#
#									#
#########################################################################


FILES =  logics-ZF.tex ../Logics/syntax.tex FOL.tex ZF.tex\
	 ../rail.sty ../proof.sty ../iman.sty ../extra.sty

logics-ZF.dvi.gz:   $(FILES) 
	test -r isabelle_zf.eps || ln -s ../gfx/isabelle_zf.eps .
	-rm logics-ZF.dvi*
	latex logics-ZF
	rail logics-ZF
	bibtex logics-ZF
	latex logics-ZF
	latex logics-ZF
	../sedindex logics-ZF
	latex logics-ZF
	gzip -f logics-ZF.dvi

dist:   $(FILES) 
	test -r isabelle_zf.eps || ln -s ../gfx/isabelle_zf.eps .
	-rm logics-ZF.dvi*
	latex logics-ZF
	latex logics-ZF
	../sedindex logics-ZF
	latex logics-ZF

clean:
	@rm *.aux *.log *.toc *.idx *.rai

