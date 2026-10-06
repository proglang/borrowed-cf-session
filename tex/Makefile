.PHONY: build
build: lhs2tex
	latexmk -pdf popl2027-supplement.tex
	latexmk -pdf popl2027.tex

FMT_FILES := $(wildcard lhs2tex/*.fmt)
LHS_FILES := $(wildcard */*.lhs.tex)

.PHONY: lhs2tex
lhs2tex: $(LHS_FILES:%.lhs.tex=%.tex)

.PHONY: lhs2tex-watch
lhs2tex-watch:
	for f in $(FMT_FILES) $(LHS_FILES); do echo $$f; done | entr $(MAKE) lhs2tex

%.tex: %.lhs.tex $(FMT_FILES)
	lhs2TeX -P :lhs2tex $< -o $@

.PHONY: clean
clean:
	latexmk -c

.PHONY: distclean
distclean: clean
	rm -f $(LHS_FILES:%.lhs.tex=%.tex)
