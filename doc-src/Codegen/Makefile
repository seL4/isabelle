
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

$(NAME).dvi: $(FILES) isabelle_isar.eps Thy/pictures/architecture.eps Thy/pictures/adaption.eps
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_isar.pdf Thy/pictures/architecture.pdf Thy/pictures/adaption.pdf
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)

Thy/pictures/%.dvi: Thy/pictures/%.tex
	latex -output-directory=$(dir $@) $<

Thy/pictures/%.eps: Thy/pictures/%.dvi
	dvips -E -o $@ $<

Thy/pictures/%.pdf: Thy/pictures/%.eps
	epstopdf --outfile=$@ $<
