#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = axclass

FILES = axclass.tex body.tex ../iman.sty ../extra.sty ../pdfsetup.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_isar.eps
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_isar.pdf
	$(PDFLATEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
