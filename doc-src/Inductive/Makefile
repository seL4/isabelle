#  $Id$
#########################################################################
#									#
#	Makefile for the report "A Fixedpoint Approach ..."		#
#									#
#########################################################################


FILES =  ind-defs.tex ../proof.sty ../iman.sty ../extra.sty

ind-defs.dvi.gz:   $(FILES) 
	-rm ind-defs.dvi.gz
	latex209 ind-defs
	bibtex ind-defs
	latex209 ind-defs
	latex209 ind-defs
	gzip -f ind-defs.dvi
