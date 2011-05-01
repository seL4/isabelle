
## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = main

FILES = ../../lib/texinputs/isabelle.sty ../../lib/texinputs/isabellesym.sty ../pdfsetup.sty $(NAME).tex	\
  Docs/document/Main_Doc.tex

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES)
	$(PDFLATEX) $(NAME)
