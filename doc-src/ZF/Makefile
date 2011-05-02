
## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = logics-ZF
FILES = logics-ZF.tex ../Logics/syntax.tex FOL.tex ZF.tex logics.sty	\
  ../proof.sty ../iman.sty ../extra.sty ../ttbox.sty	\
  ../../lib/texinputs/isabelle.sty ../../lib/texinputs/isabellesym.sty ../pdfsetup.sty ../manual.bib

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_zf.eps
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_zf.pdf
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
