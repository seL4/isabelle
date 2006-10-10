#
# $Id$
#

## targets

default: dvi


## dependencies

include ../../Makefile.in

isabelle_isar.eps:
	test -r isabelle_isar.eps || ln -s ../../gfx/isabelle_isar.eps .

isabelle_isar.pdf:
	test -r isabelle_isar.pdf || ln -s ../../gfx/isabelle_isar.pdf .

NAME = classes

FILES = $(NAME).tex classes.tex Thy/document/Classes.tex \
  style.sty ../../iman.sty ../../extra.sty ../../isar.sty \
  ../../manual.bib ../../proof.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_isar.eps
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_isar.pdf
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
