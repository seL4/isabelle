
## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = codegen

FILES = $(NAME).tex Thy/document/*.tex \
  style.sty ../iman.sty ../extra.sty ../isar.sty \
  ../isabelle.sty ../isabellesym.sty ../pdfsetup.sty \
  ../manual.bib ../proof.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_isar.eps codegen_process.ps
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_isar.pdf codegen_process.pdf
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
