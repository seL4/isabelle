#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = system
FILES = system.tex basics.tex misc.tex fonts.tex present.tex \
	../iman.sty ../extra.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle.eps
	touch $(NAME).ind
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle.pdf
	touch $(NAME).ind
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(PDFLATEX) $(NAME)
