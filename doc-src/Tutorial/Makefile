#
# $Id$
#

## targets

default: dvi
dist: dvi


## dependencies

include ../Makefile.in

NAME = tutorial
FILES = tutorial.tex basics.tex fp.tex appendix.tex \
	../iman.sty ttbox.sty extra.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_hol.eps
	touch $(NAME).ind
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)
