#
# $Id$
#

## targets

default: dvi
dist: dvi


## dependencies

include ../Makefile.in

NAME = intro
FILES = intro.tex foundations.tex getting.tex advanced.tex \
	../proof.sty ../iman.sty ../extra.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle.eps
	touch $(NAME).ind
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)
