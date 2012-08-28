## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = isar-ref

FILES = isar-ref.tex style.sty Thy/document/Framework.tex		\
  Thy/document/Generic.tex Thy/document/HOLCF_Specific.tex		\
  Thy/document/HOL_Specific.tex Thy/document/ML_Tactic.tex		\
  Thy/document/Proof.tex Thy/document/Quick_Reference.tex		\
  Thy/document/Spec.tex Thy/document/Synopsis.tex			\
  Thy/document/Inner_Syntax.tex		\
  Thy/document/Preface.tex Thy/document/Document_Preparation.tex	\
  Thy/document/Misc.tex Thy/document/Outer_Syntax.tex			\
  Thy/document/Symbols.tex ../isar.sty ../proof.sty ../iman.sty		\
  ../extra.sty ../ttbox.sty ../../lib/texinputs/isabelle.sty		\
  ../../lib/texinputs/isabellesym.sty					\
  ../../lib/texinputs/railsetup.sty ../pdfsetup.sty ../manual.bib

OUTPUT = syms.tex

syms.tex: showsymbols ../../lib/texinputs/isabellesym.sty
	@./showsymbols <../../lib/texinputs/isabellesym.sty >syms.tex


dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_isar.eps syms.tex
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_isar.pdf syms.tex
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
