#  $Id$
#########################################################################
#									#
#	Makefile for the report "A Fixedpoint Approach ..."		#
#									#
#########################################################################

dvi: dist

pdf:

FILES =  ind-defs.tex ../proof.sty ../iman.sty ../extra.sty

ind-defs.dvi.gz:   $(FILES) 
	-rm ind-defs.dvi.gz
	latex ind-defs
	bibtex ind-defs
	latex ind-defs
	latex ind-defs
	gzip -f ind-defs.dvi

dist:   $(FILES) 
	-rm ind-defs.dvi*
	latex ind-defs
	latex ind-defs

clean:
	@rm *.aux *.log *.toc

