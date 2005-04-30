#
# $Id$
#

## targets

default: dvi

## dependencies

include ../../../Makefile.in

dvi: ../../isar-overview.dvi

../../isar-overview.dvi: *.tex *.sty *.bib
	$(LATEX) root
	$(BIBTEX) root
	$(LATEX) root
	$(LATEX) root
	mv root.dvi ../../isar-overview.dvi

pdf: ../../isar-overview.pdf

../../isar-overview.pdf: *.tex *.sty *.bib
	$(PDFLATEX) root
	$(BIBTEX) root
	$(PDFLATEX) root
	$(PDFLATEX) root
	mv root.pdf ../../isar-overview.pdf