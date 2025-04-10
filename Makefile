default: main

main:
	pdflatex main
	bibtex main
	pdflatex main
	pdflatex main
	rm *.aux *.log *.out *.bbl *.blg
