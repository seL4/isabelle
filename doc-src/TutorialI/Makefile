#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

SEDINDEX = ./isa-index

NAME = tutorial
FILES = tutorial.tex basics.tex fp.tex appendix.tex \
	Advanced/advanced.tex \
	CTL/ctl.tex \
	Inductive/inductive.tex Inductive/even-example.tex \
	Inductive/advanced-examples.tex \
	Protocol/protocol.tex \
	Rules/rules.tex Sets/sets.tex \
	Types/numerics.tex Types/types.tex \
	Documents/documents.tex \
	../iman.sty ../ttbox.sty ../extra.sty \
	isabelle.sty isabellesym.sty ../pdfsetup.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_hol.eps Types/typedef.eps
	@test -r typedef.eps || ln -s ../gfx/typedef.ps .
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_hol.pdf Types/typedef.pdf
	@test -r typedef.pdf || ln -s ../gfx/typedef.pdf .
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
