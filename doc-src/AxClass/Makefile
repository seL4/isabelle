#
# $Id$
#

## targets

default: dvi
dist: dvi


## dependencies

include ../Makefile.in

NAME = axclass
FILES = axclass.tex style.tex

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
