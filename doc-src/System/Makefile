#  $Id$
#########################################################################
#									#
#	Makefile for the report "The Isabelle System Manual"		#
#									#
#########################################################################


FILES =  system.tex \
	 ../iman.sty ../extra.sty

system.dvi.gz:   $(FILES) 
	-rm system.dvi*
	latex system
	rail system
	bibtex system
	latex system
	latex system
	../sedindex system
	latex system
	gzip -f system.dvi

dist:   $(FILES) 
	-rm system.dvi*
	latex system
	latex system
	../sedindex system
	latex system

clean:
	@rm *.aux *.log *.toc *.idx
