#
# $Id$
#

## targets

default: dvi
dist: dvi


## dependencies

include ../Makefile.in

NAME = ref
FILES = ref.tex introduction.tex goals.tex tactic.tex tctical.tex \
	thm.tex theories.tex defining.tex syntax.tex substitution.tex \
	simplifier.tex classical.tex theory-syntax.tex \
	../rail.sty ../proof.sty ../iman.sty ../extra.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle.eps
	touch $(NAME).ind
	$(LATEX) $(NAME)
	$(RAIL) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)
