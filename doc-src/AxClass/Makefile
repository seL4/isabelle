#  $Id$
#########################################################################
#									#
#	Makefile for the report "Introduction to Isabelle"		#
#									#
#########################################################################


FILES =  axclass.tex style.tex

axclass.dvi.gz:   $(FILES)
	-rm axclass.dvi*
	latex axclass
	latex axclass
	gzip -f axclass.dvi

dist:   $(FILES)
	-rm axclass.dvi*
	latex axclass
	latex axclass

clean:
	@rm *.aux *.log
