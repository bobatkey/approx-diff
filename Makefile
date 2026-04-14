.PHONY: main notes clean # otherwise confused by folders with the same name

default: main

main: main.pdf
notes: notes.pdf

# -out2dir unsupported on default Mac installation
LATEXMK_OPTS:=-output-format=pdf -outdir=_latex
export BIBINPUTS=..:

MAIN_DEPS:=$(wildcard main/*.tex) $(wildcard fig/*.tex) macros.tex bib.bib

main.pdf: main.tex $(MAIN_DEPS)
	latexmk $(LATEXMK_OPTS) main
	cd _latex && bibtex main
	latexmk $(LATEXMK_OPTS) -g main
	cp _latex/main.pdf .

NOTES_DEPS:=$(wildcard notes/*.tex) $(wildcard fig/*.tex) macros.tex bib.bib

notes.pdf: notes.tex $(NOTES_DEPS)
	latexmk $(LATEXMK_OPTS) notes
	cd _latex && bibtex notes
	latexmk $(LATEXMK_OPTS) -g notes
	cp _latex/notes.pdf .

clean:
	rm -rf _latex
	rm -f main.pdf
	rm -f notes.pdf
