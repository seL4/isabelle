#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = logics-ZF
FILES = logics-ZF.tex ../Logics/syntax.tex FOL.tex ZF.tex \
	../rail.sty ../proof.sty ../iman.sty ../extra.sty ../manual.bib

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_zf.eps
	$(LATEX) $(NAME)
	$(RAIL) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_zf.pdf
	$(PDFLATEX) $(NAME)
	$(RAIL) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
