TEX = latex
TMP = *.aux *.dvi *.log *.bbl *.blg *.toc
DOCS = guide
GEN = $(addsuffix .ps, $(DOCS)) $(addsuffix .pdf, $(DOCS))

all : $(GEN)

%.toc : %.tex
	latex $*

%.dvi: %.tex %.toc
	latex $*

%.ps : %.dvi %.toc
	dvips $< -t letter -o $@

%.pdf : %.tex %.toc
	pdflatex $*

clean : 
	rm -rf *~ $(TMP)

spotless : clean
	rm -rf $(GEN)
