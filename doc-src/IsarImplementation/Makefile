
## targets

default: dvi


## dependencies

include ../Makefile.in

MAKEGLOSSARY = ./makeglossary

NAME = implementation

FILES = implementation.tex Thy/document/Prelim.tex			\
  Thy/document/Logic.tex Thy/document/Tactic.tex			\
  Thy/document/Proof.tex Thy/document/Local_Theory.tex			\
  Thy/document/Integration.tex style.sty ../iman.sty ../extra.sty	\
  ../isar.sty ../isabelle.sty ../isabellesym.sty ../pdfsetup.sty	\
  ../manual.bib ../proof.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_isar.eps
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(MAKEGLOSSARY) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_isar.pdf
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(MAKEGLOSSARY) $(NAME)
	$(SEDINDEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
