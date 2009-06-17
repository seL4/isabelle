#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

SEDINDEX = ./isa-index

NAME = tutorial
FILES = tutorial.tex basics.tex fp.tex appendix.tex			\
	Advanced/advanced.tex CTL/ctl.tex Inductive/inductive.tex	\
	Inductive/document/AB.tex Inductive/document/Advanced.tex	\
	Inductive/document/Even.tex Inductive/document/Mutual.tex	\
	Inductive/document/Star.tex Protocol/protocol.tex		\
	Protocol/document/Event.tex Protocol/document/Message.tex	\
	Protocol/document/Public.tex Protocol/document/NS_Public.tex	\
	Rules/rules.tex Sets/sets.tex Types/numerics.tex		\
	Types/types.tex Types/document/Overloading.tex \
	Types/document/Axioms.tex Documents/documents.tex Misc/document/appendix.tex ../iman.sty	\
	../ttbox.sty ../extra.sty ../isabelle.sty ../isabellesym.sty	\
	../pdfsetup.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_hol.eps typedef.ps
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_hol.pdf typedef.pdf
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
