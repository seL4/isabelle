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

FILES = locales.tex Locales/generated/root.bib \
  Locales/generated/session.tex Locales/generated/Locales.tex \
  Locales/generated/isabelle.sty Locales/generated/isabellesym.sty \
  Locales/generated/pdfsetup.sty 

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES)
	env TEXINPUTS=$(TEXPATH) $(LATEX) $(NAME)
	env BIBINPUTS=$(TEXPATH) $(BIBTEX) $(NAME)
	env TEXINPUTS=$(TEXPATH) $(LATEX) $(NAME)
	env TEXINPUTS=$(TEXPATH) $(LATEX) $(NAME)
	env TEXINPUTS=$(TEXPATH) $(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES)
	env TEXINPUTS=$(TEXPATH) $(PDFLATEX) $(NAME)
	env BIBINPUTS=$(TEXPATH) $(BIBTEX) $(NAME)
	env TEXINPUTS=$(TEXPATH) $(PDFLATEX) $(NAME)
	env TEXINPUTS=$(TEXPATH) $(PDFLATEX) $(NAME)
	env TEXINPUTS=$(TEXPATH) $(PDFLATEX) $(NAME)
