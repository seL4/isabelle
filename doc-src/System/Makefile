#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = system
FILES = system.tex basics.tex misc.tex fonts.tex present.tex \
	../iman.sty ../extra.sty ../manual.bib

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle.eps
	touch $(NAME).ind
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle.pdf
	touch $(NAME).ind
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(PDFLATEX) $(NAME)
