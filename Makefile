default: notes

notes:
	pdflatex notes.tex
	pdflatex notes.tex
	rm notes.aux notes.log notes.out
