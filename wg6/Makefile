SRC := abstract.tex \
       references.bib

all: abstract.pdf

%.tex : %.lagda lib.fmt
	lhs2TeX --agda $< > $@

abstract.tex : abstract.lagda lib.fmt
	lhs2TeX --agda abstract.lagda > abstract.tex

abstract.pdf: $(SRC)
	latexmk -pdf -f -pdflatex='pdflatex -halt-on-error' $<
	#bibtex $(patsubst %.tex,%,$<) && \
	#TEXINPUTS=./latex:$$TEXINPUTS pdflatex $< ;\
	#TEXINPUTS=./latex:$$TEXINPUTS pdflatex $< ;\

clean:
	$(RM) *.aux *.log *.out *.vrb paper.pdf \
              *.bbl *.blg *.fdb_latexmk *.toc *.fls *.cut 

