#
# $Id$
#

## targets

default: dvi
dist: dvi


## dependencies

include ../Makefile.in

NAME = logics-ZF
FILES = logics-ZF.tex ../Logics/syntax.tex FOL.tex ZF.tex \
	../rail.sty ../proof.sty ../iman.sty ../extra.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_zf.eps
	touch $(NAME).ind
	$(LATEX) $(NAME)
	$(RAIL) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)
