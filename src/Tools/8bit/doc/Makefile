###############################################
# Title:      Tools/8bit/doc/Makefile
# ID:         $Id$
# Author:     David von Oheimb
# Copyright   1996 TU Muenchen
#
# Makefile for the document files
###############################################

# operate silently
MAKEFLAGS='s'

LATEX=latex2e
ISA2LATEX=isa2latex

CHECKOUT=co

.SUFFIXES: $(SUFFIXES) .itex .thy .ML .tex .dvi

.itex.tex:
	$(ISA2LATEX) -x -e -o $@ $<
.thy.tex .ML.tex:
	$(ISA2LATEX) -s -e -f '\oddsidemargin-1cm{}\evensidemargin-1cm' -o $@ $<
.tex.dvi:
	$(LATEX) $<

FONTDOCFILES = fontindex.dvi keyindex.dvi fkmatrix.dvi

fontdocfiles: $(FONTDOCFILES)

manual: manual.tex manual.dvi

manual.tex: manual.itex

clean:
	rm -f *.aux *.log
