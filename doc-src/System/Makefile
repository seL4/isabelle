#
# $Id$
#

## targets

default: dvi
dist: dvi


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
