#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = ind-defs
FILES = ind-defs.tex ../proof.sty ../iman.sty ../extra.sty ../ttbox.sty ../manual.bib

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES)
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES)
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
