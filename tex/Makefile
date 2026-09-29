build: code-snippets.tex
	latexmk -pdf popl2027-supplement.tex
	latexmk -pdf popl2027.tex

code-snippets.tex: code-snippets.lhs lineno.fmt
	lhs2TeX $< -o $@
