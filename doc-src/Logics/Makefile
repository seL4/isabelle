#
# $Id$
#

## targets

default: dvi
dist: dvi


## dependencies

include ../Makefile.in

NAME = logics
FILES = logics.tex preface.tex syntax.tex LK.tex CTT.tex \
	../proof.sty ../iman.sty ../extra.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_hol.eps
	touch $(NAME).ind
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)
