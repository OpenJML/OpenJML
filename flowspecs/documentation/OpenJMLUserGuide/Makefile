
PDF="C:/Program Files (x86)/MiKTeX 2.9/miktex/bin/pdflatex.exe"
BIB="C:/Program Files (x86)/MiKTeX 2.9/miktex/bin/bibtex.exe"

R=OpenJMLUserGuide

once:
	${PDF} -interaction=nonstopmode $R.tex

all:
	${PDF} -interaction=nonstopmode $R.tex
	${PDF} -interaction=nonstopmode $R.tex

bib:
	${BIB} $R

clean:
	rm *.log *.aux *.out *.pdf *.bbl *.blg *.toc

