.PHONY default: main notes # otherwise confused by folders with the same name

main:
	pdflatex main
	bibtex main
	pdflatex main
	pdflatex main
	rm *.aux *.log *.out *.bbl *.blg

notes:
	pdflatex notes
	bibtex notes
	pdflatex notes
	pdflatex notes
	rm *.aux *.log *.out *.bbl *.blg
