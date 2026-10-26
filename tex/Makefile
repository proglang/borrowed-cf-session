LHS2TEX= lhs2TeX
.PHONY: build
build: lhs2tex
	latexmk -pdf popl2027-supplement.tex
	latexmk -pdf popl2027.tex

FMT_FILES := $(wildcard lhs2tex/*.fmt)
LHS_FILES := $(wildcard */*.lhs.tex)

.PHONY: diff
diff: lhs2tex
	@if [ -z "$(DIFF_DIR)" ]; then echo 'usage: make DIFF_DIR=... diff'; false; fi
	latexdiff --flatten --append-safecmd=RuleName $(DIFF_DIR)/popl2027.tex popl2027.tex > popl2027-diff.tex
	latexmk -pdf popl2027-diff

.PHONY: lhs2tex
lhs2tex: $(LHS_FILES:%.lhs.tex=%.tex)

.PHONY: lhs2tex-watch
lhs2tex-watch:
	@printf '%s\n' $(FMT_FILES) $(LHS_FILES) | entr $(MAKE) lhs2tex

%.tex: %.lhs.tex $(FMT_FILES)
	$(LHS2TEX) -P :lhs2tex $< -o $@

.PHONY: clean
clean:
	latexmk -c

.PHONY: distclean
distclean: clean
	rm -f $(LHS_FILES:%.lhs.tex=%.tex)
