
## targets

default: dvi


## dependencies

include ../Makefile.in

SEDINDEX = ./isa-index

NAME = tutorial
FILES = tutorial.tex basics.tex fp.tex appendix.tex			\
	Advanced/advanced.tex CTL/ctl.tex Inductive/inductive.tex	\
	document/AB.tex document/Advanced.tex document/Even.tex		\
	document/Mutual.tex document/Star.tex Protocol/protocol.tex	\
	document/Event.tex document/Message.tex document/Public.tex	\
	document/NS_Public.tex Rules/rules.tex Sets/sets.tex		\
	Types/numerics.tex Types/types.tex document/Overloading.tex	\
	document/Axioms.tex Documents/documents.tex			\
	document/appendix.tex ../iman.sty ../ttbox.sty ../extra.sty	\
	../../lib/texinputs/isabelle.sty				\
	../../lib/texinputs/isabellesym.sty ../pdfsetup.sty

ToyList2/ToyList.thy: ToyList2/ToyList1 ToyList2/ToyList2
	cat ToyList2/ToyList1 ToyList2/ToyList2 > ToyList2/ToyList.thy


dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_hol.eps typedef.ps ToyList2/ToyList.thy
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_hol.pdf typedef.pdf ToyList2/ToyList.thy
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(SEDINDEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
