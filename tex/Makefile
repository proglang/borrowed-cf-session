build: code-snippets.tex
	latexmk -pdf popl2027-supplement.tex
	latexmk -pdf popl2027.tex

FMT_FILES := $(wildcard *.fmt)

.PHONY: lhs2tex
lhs2tex: code-snippets.tex sec/motivation.tex

%.tex: %.lhs.tex $(FMT_FILES)
	lhs2TeX $< -o $@
