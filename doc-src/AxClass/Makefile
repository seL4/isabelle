#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = axclass
FILES = axclass.tex style.tex

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES)
	$(PDFLATEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
