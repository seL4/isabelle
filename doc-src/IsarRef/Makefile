#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = isar-ref

FILES = isar-ref.tex intro.tex basics.tex syntax.tex pure.tex \
	simplifier.tex classical.tex hol.tex \
	../rail.sty ../proof.sty ../iman.sty ../extra.sty ../manual.bib

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_isar.eps
	touch $(NAME).ind
	$(LATEX) $(NAME)
	$(RAIL) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_isar.pdf
	touch $(NAME).ind
	$(PDFLATEX) $(NAME)
	$(RAIL) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
