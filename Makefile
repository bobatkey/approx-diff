.PHONY: main notes clean # otherwise confused by folders with the same name

default: main

main: main.pdf
notes: notes.pdf

# -out2dir unsupported on default Mac installation
LATEXMK_OPTS:=-output-format=pdf -outdir=_latex

MAIN_DEPS:=$(wildcard main/*.tex) $(wildcard fig/*.tex) macros.tex bib.bib

main.pdf: main.tex $(MAIN_DEPS)
	latexmk $(LATEXMK_OPTS) main
	cp _latex/main.pdf .

NOTES_DEPS:=$(wildcard notes/*.tex) $(wildcard fig/*.tex) macros.tex bib.bib

notes.pdf: notes.tex $(NOTES_DEPS)
	latexmk $(LATEXMK_OPTS) notes
	cp _latex/notes.pdf .

clean:
	rm -rf _latex
	rm -f main.pdf
	rm -f notes.pdf

js:
	pushd agda && \
	agda --js --compile-dir=_js_build src/example.agda --js-verify
