.PHONY: main notes clean # otherwise confused by folders with the same name

default: main

main: main.pdf
notes: notes.pdf

MAIN_DEPS:=$(wildcard main/*.tex) bib.bib

main.pdf: main.tex $(MAIN_DEPS)
	pdflatex main
	bibtex main
	pdflatex main
	pdflatex main
	rm *.aux *.log *.out *.bbl *.blg

NOTES_DEPS:=$(wildcard notes/*.tex) bib.bib

notes.pdf: notes.tex $(NOTES_DEPS)
	pdflatex notes
	bibtex notes
	pdflatex notes
	pdflatex notes
	rm *.aux *.log *.out *.bbl *.blg

clean:
	rm -f main.pdf
	rm -f notes.pdf
