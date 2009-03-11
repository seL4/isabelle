#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

SRC = ../../src/HOL/Docs/generated

NAME = main

FILES = $(NAME).tex Main_Doc.tex \
  isabelle.sty isabellesym.sty pdfsetup.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES)
	$(PDFLATEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)

isabelle.sty:
	ln ../isabelle.sty .

isabellesym.sty:
	ln ../isabellesym.sty .

pdfsetup.sty:
	ln ../pdfsetup.sty .

copy:
	cp $(SRC)/Main_Doc.tex Main_Doc.tex
	cp $(SRC)/root.tex main.tex
