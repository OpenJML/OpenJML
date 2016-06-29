
PDF="/Library/TeX/texbin/pdflatex"
BIB="/Library/TeX/texbin/bibtex"
HTL="/Library/TeX/texbin/htlatex"
ARGS="macro.hva"

R=OpenJMLUserGuide

all: clean pdf html

once:
	${PDF} -interaction=nonstopmode $R.tex

pdf:
	-${PDF} -interaction=nonstopmode $R.tex
	-${PDF} -interaction=nonstopmode $R.tex
	make bib
	-${PDF} -interaction=nonstopmode $R.tex


html:
	${HTL} $R "html, fn-in, index=2"
	./fix < $R.html > $R-onepage.html
	${HTL} $R "html, frames, next, 3, index=2"
	./fix < $R.html > x.html
	mv x.html $R.html

## NOTE: fn-in appears to be incompatible with frames; mouseover does not seem to work
##	${HTL} $R "html, frames, 3, fn-in, mouseover, next, index=2"

bib:
	${BIB} $R

clean:
	rm -f *.log *.aux *.out *.pdf *.bbl *.blg *.toc *.html *.class *.css *backup  *.4* *.div *.idv *.lg *.tmp *.xref

