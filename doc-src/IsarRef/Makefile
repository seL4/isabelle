#
# $Id$
#

## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = isar-ref

FILES = isar-ref.tex style.sty Thy/document/Generic.tex			\
  Thy/document/HOLCF_Specific.tex Thy/document/HOL_Specific.tex		\
  Thy/document/ML_Tactic.tex Thy/document/Proof.tex			\
  Thy/document/Quick_Reference.tex Thy/document/Spec.tex		\
  Thy/document/ZF_Specific.tex Thy/document/Introduction.tex		\
  Thy/document/Document_Preparation.tex Thy/document/Misc.tex		\
  Thy/document/Outer_Syntax.tex ../isar.sty ../rail.sty			\
  ../railsetup.sty ../proof.sty ../iman.sty ../extra.sty ../ttbox.sty	\
  ../isabelle.sty ../isabellesym.sty ../pdfsetup.sty ../manual.bib

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_isar.eps
	$(LATEX) $(NAME)
	$(RAIL) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_isar.pdf
	$(PDFLATEX) $(NAME)
	$(RAIL) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
