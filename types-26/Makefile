.PHONY: main

main:
	agda --latex --latex-dir=./ main.lagda.tex
	lualatex main.tex
	bibtex main.aux
	lualatex main.tex
	lualatex main.tex