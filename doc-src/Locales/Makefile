#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = locales

FILES = Locales/document/root.tex Locales/document/root.bib \
  Locales/document/session.tex Locales/document/Examples.tex \
  Locales/document/Examples1.tex Locales/document/Examples2.tex \
  Locales/document/Examples3.tex \
  ../isabelle.sty ../isabellesym.sty ../pdfsetup.sty 

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES)
	cd Locales/document && \
	$(LATEX) root && \
	$(BIBTEX) root && \
	$(LATEX) root && \
	$(LATEX) root && \
	$(LATEX) root
	mv Locales/document/root.dvi $(NAME).dvi

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES)
	cd Locales/document && \
	$(PDFLATEX) root && \
	$(BIBTEX) root && \
	$(PDFLATEX) root && \
	$(PDFLATEX) root && \
	$(PDFLATEX) root
	mv Locales/document/root.pdf $(NAME).pdf
