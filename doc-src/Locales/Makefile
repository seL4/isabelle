#
# $Id$
#

## targets

default: dvi

## paths

TEXPATH = Locales/document/:

## dependencies

include ../Makefile.in

NAME = locales

FILES = Locales/document/root.tex Locales/document/root.bib \
  Locales/document/session.tex Locales/document/Locales.tex \
  Locales/document/isabelle.sty Locales/document/isabellesym.sty \
  Locales/document/pdfsetup.sty 

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
