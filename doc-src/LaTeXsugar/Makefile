#
# $Id$
#

## targets

default: dvi

## paths

SRCPATH = Sugar/generated

## dependencies

include ../Makefile.in

NAME = sugar

FILES = Sugar/generated/root.tex Sugar/generated/root.bib \
	      Sugar/generated/mathpartir.sty Sugar/generated/LaTeXsugar.tex \
        Sugar/generated/OptionalSugar.tex

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES)
	cd Sugar/generated; \
	$(LATEX) root; \
	$(BIBTEX) root; \
	$(LATEX) root; \
	$(LATEX) root
	cp $(SRCPATH)/root.dvi $(NAME).dvi

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES)
	cd Sugar/generated; \
	$(PDFLATEX) root; \
	$(BIBTEX) root; \
	$(PDFLATEX) root; \
	$(PDFLATEX) root
	cp $(SRCPATH)/root.pdf $(NAME).pdf

