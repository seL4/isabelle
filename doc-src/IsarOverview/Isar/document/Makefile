#
# $Id$
#

## targets

default: dvi

## dependencies

include ../../../Makefile.in

dvi: ../../isar-overview.dvi

../../isar-overview.dvi: root.dvi
	cp root.dvi ../../isar-overview.dvi

root.dvi: *.tex *.sty *.bib
	$(LATEX) root
	$(BIBTEX) root
	$(LATEX) root
	$(LATEX) root

pdf: ../../isar-overview.pdf

../../isar-overview.pdf: root.pdf
	cp root.pdf ../../isar-overview.pdf

root.pdf: *.tex *.sty *.bib
	$(PDFLATEX) root
	$(BIBTEX) root
	$(PDFLATEX) root
	$(PDFLATEX) root
