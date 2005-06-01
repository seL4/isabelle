#
# $Id$
#

## targets

default: dvi

## paths

TEXPATH = Locales/generated/:

## dependencies

include ../Makefile.in

NAME = locales

FILES = Locales/generated/root.tex Locales/generated/root.bib \
  Locales/generated/session.tex Locales/generated/Locales.tex \
  Locales/generated/isabelle.sty Locales/generated/isabellesym.sty \
  Locales/generated/pdfsetup.sty 

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES)
	env TEXINPUTS=$(TEXPATH) $(LATEX) root
	env BIBINPUTS=$(TEXPATH) $(BIBTEX) root
	env TEXINPUTS=$(TEXPATH) $(LATEX) root
	env TEXINPUTS=$(TEXPATH) $(LATEX) root
	env TEXINPUTS=$(TEXPATH) $(LATEX) root
	mv root.dvi $(NAME).dvi

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES)
	env TEXINPUTS=$(TEXPATH) $(PDFLATEX) root
	env BIBINPUTS=$(TEXPATH) $(BIBTEX) root
	env TEXINPUTS=$(TEXPATH) $(PDFLATEX) root
	env TEXINPUTS=$(TEXPATH) $(PDFLATEX) root
	env TEXINPUTS=$(TEXPATH) $(PDFLATEX) root
	mv root.pdf $(NAME).pdf
