#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = system
FILES = system.tex Thy/document/Basics.tex misc.tex present.tex symbols.tex \
	../iman.sty ../extra.sty ../ttbox.sty ../manual.bib

OUTPUT = syms.tex

syms.tex: showsymbols ../isabellesym.sty
	@./showsymbols <../isabellesym.sty >syms.tex

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle.eps syms.tex
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle.pdf syms.tex
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(PDFLATEX) $(NAME)
