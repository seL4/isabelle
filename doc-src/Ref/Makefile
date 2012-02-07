
## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = ref
FILES = ref.tex tactic.tex thm.tex syntax.tex		\
	substitution.tex simplifier.tex classical.tex ../proof.sty	\
	../iman.sty ../extra.sty ../ttbox.sty ../manual.bib

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle.eps
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle.pdf
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
