#
# $Id$
#

## targets

default: dvi

## dependencies

include ../../../Makefile.in

dvi: ../../isar-overview.dvi

../../isar-overview.dvi: root.dvi
	mv root.dvi ../../isar-overview.dvi

root.dvi: *.tex *.sty *.bib
	$(LATEX) root
	$(BIBTEX) root
	$(LATEX) root
	$(LATEX) root

pdf: ../../isar-overview.pdf

../../isar-overview.pdf: root.pdf
	mv root.pdf ../../isar-overview.pdf

root.pdf: *.tex *.sty *.bib
	$(PDFLATEX) root
	$(BIBTEX) root
	$(PDFLATEX) root
	$(PDFLATEX) root
