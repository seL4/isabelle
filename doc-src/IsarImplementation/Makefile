#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

MAKEGLOSSARY = ./makeglossary

NAME = implementation

FILES = implementation.tex intro.tex Thy/document/prelim.tex Thy/document/logic.tex \
  Thy/document/tactic.tex Thy/document/proof.tex Thy/document/locale.tex \
  Thy/document/integration.tex style.sty ../iman.sty ../extra.sty ../isar.sty \
  ../manual.bib ../proof.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_isar.eps
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(MAKEGLOSSARY) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_isar.pdf
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(MAKEGLOSSARY) $(NAME)
	$(SEDINDEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
