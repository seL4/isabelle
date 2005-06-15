#
# $Id$
#

## targets

default: dvi

## paths

SRCPATH = Sugar/document

## dependencies

include ../Makefile.in

NAME = sugar

FILES = Sugar/document/root.tex Sugar/document/root.bib \
        Sugar/document/mathpartir.sty Sugar/document/LaTeXsugar.tex \
        Sugar/document/OptionalSugar.tex Sugar/document/Sugar.tex

GARBAGE = Sugar/document/*.aux Sugar/document/*.log Sugar/document/*.toc \
          Sugar/document/*.idx Sugar/document/*.bbl Sugar/document/*.blg \
          Sugar/document/*.out

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES)
	cd Sugar/document; \
	$(LATEX) root; \
	$(BIBTEX) root; \
	$(LATEX) root; \
	$(LATEX) root
	mv $(SRCPATH)/root.dvi $(NAME).dvi

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES)
	cd Sugar/document; \
	$(PDFLATEX) root; \
	$(BIBTEX) root; \
	$(PDFLATEX) root; \
	$(PDFLATEX) root
	mv $(SRCPATH)/root.pdf $(NAME).pdf

