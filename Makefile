default: main

main:
	pdflatex notes
	bibtex notes
	pdflatex notes
	pdflatex notes
	rm notes.aux notes.log notes.out
