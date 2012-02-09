
## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = implementation

FILES = ../extra.sty ../iman.sty ../../lib/texinputs/isabelle.sty	\
  ../../lib/texinputs/isabellesym.sty					\
  ../../lib/texinputs/railsetup.sty ../isar.sty ../manual.bib		\
  ../pdfsetup.sty ../proof.sty Thy/document/Eq.tex			\
  Thy/document/Integration.tex Thy/document/Isar.tex			\
  Thy/document/Local_Theory.tex Thy/document/Logic.tex			\
  Thy/document/Prelim.tex Thy/document/Proof.tex			\
  Thy/document/Syntax.tex Thy/document/Tactic.tex implementation.tex	\
  style.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_isar.eps
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_isar.pdf
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
