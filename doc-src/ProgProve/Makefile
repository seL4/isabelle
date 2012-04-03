## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = prog-prove

FILES = prog-prove.tex prog-prove.bib Thys/document/*.tex prelude.tex \
  svmono.cls mathpartir.sty isabelle.sty isabellesym.sty Thys/MyList.thy

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_hol.eps bang.eps
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_hol.pdf bang.pdf
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
