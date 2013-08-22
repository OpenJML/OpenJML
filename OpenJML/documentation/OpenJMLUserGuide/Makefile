
PDF="C:/Program Files (x86)/MiKTeX 2.9/miktex/bin/pdflatex.exe"
BIB="C:/Program Files (x86)/MiKTeX 2.9/miktex/bin/bibtex.exe"
HEV="C:/Hevea/HEVEA.BAT"
HACHA="C:/Hevea/HACHA.BAT"
ARGS="macro.hva"

R=OpenJMLUserGuide

all: pdf html

once:
	${PDF} -interaction=nonstopmode $R.tex

pdf:
	${PDF} -interaction=nonstopmode $R.tex
	${PDF} -interaction=nonstopmode $R.tex
	make bib
	${PDF} -interaction=nonstopmode $R.tex


html:
	${HEV} ${ARGS} $R.tex
	${HEV} ${ARGS} $R.tex
	javac Transform.java && java -cp "." Transform $R.html
	${HACHA} $R.html

bib:
	${BIB} $R

clean:
	rm *.log *.aux *.out *.pdf *.bbl *.blg *.toc *.html

