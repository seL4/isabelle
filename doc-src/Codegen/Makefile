
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

$(NAME).dvi: $(FILES) isabelle_isar.eps architecture.eps adaption.eps
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_isar.pdf architecture.pdf adaption.pdf
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)

architecture.dvi: Thy/pictures/architecture.tex
	latex -output-directory=$(dir $@) $<

adaption.dvi: Thy/pictures/adaption.tex
	latex -output-directory=$(dir $@) $<

architecture.eps: architecture.dvi
	dvips -E -o $@ $<

adaption.eps: adaption.dvi
	dvips -E -o $@ $<

architecture.pdf: architecture.eps
	epstopdf --outfile=$@ $<

adaption.pdf: adaption.eps
	epstopdf --outfile=$@ $<
