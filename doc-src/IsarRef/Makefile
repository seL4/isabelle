#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = isar-ref

FILES = isar-ref.tex intro.tex basics.tex syntax.tex pure.tex \
	generic.tex logics.tex refcard.tex conversion.tex \
	../isar.sty ../rail.sty ../railsetup.sty ../proof.sty \
	../iman.sty ../extra.sty ../ttbox.sty ../manual.bib

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_isar.eps
	$(LATEX) $(NAME)
	$(RAIL) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_isar.pdf
	$(PDFLATEX) $(NAME)
	$(RAIL) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
