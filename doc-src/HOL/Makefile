#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = logics-HOL
FILES = logics-HOL.tex ../Logics/syntax.tex HOL.tex \
	 ../rail.sty ../proof.sty ../iman.sty ../extra.sty ../ttbox.sty ../manual.bib

rail:
	$(RAIL) $(NAME)

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_hol.eps
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_hol.pdf
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
