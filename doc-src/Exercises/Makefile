all: gen tex

gen: g2000 g2001 g2002

tex:
	pdflatex exercises
	bibtex exercises
	pdflatex exercises
	pdflatex exercises

g2000:
	cd 2000; isatool make

g2001:
	cd 2001; isatool make

g2002:
	cd 2002; isatool make

clean:
	rm -f *.log *.aux *.bbl *.blg *.toc *.out *~

realclean: clean
	rm -rf exercises.pdf */*/generated
