#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = tutorial
FILES = tutorial.tex basics.tex fp.tex appendix.tex \
	../iman.sty ttbox.sty extra.sty

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
