default: main

main:
	pdflatex notes
	pdflatex notes
	rm notes.aux notes.log notes.out
