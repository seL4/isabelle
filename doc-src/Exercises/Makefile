all: gen pdf

gen: g0304 g2000 g2001 g2002

dvi: gen
	latex exercises
	bibtex exercises
	latex exercises
	latex exercises

pdf: gen 
	pdflatex exercises
	bibtex exercises
	pdflatex exercises
	pdflatex exercises

g0304:
	cd 0304; make

g2000:
	cd 2000; make

g2001:
	cd 2001; make

g2002:
	cd 2002; make

clean:
	rm -f *.log *.aux *.bbl *.blg *.toc *.out *~

realclean: clean
	rm -rf exercises.pdf execrcises.dvi
