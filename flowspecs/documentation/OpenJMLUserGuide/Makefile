
PDF="C:/Program Files (x86)/MiKTeX 2.9/miktex/bin/pdflatex.exe"
BIB="C:/Program Files (x86)/MiKTeX 2.9/miktex/bin/bibtex.exe"
HEV="C:/cygwin/home/dcok/mybin/HEVEA.BAT"
HACHA="C:/hevea/HACHA.BAT"
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
	${HEV} -fix ${ARGS} $R.tex |& grep -v "Warning: minipage"
	javac Transform.java && java -cp "." Transform $R.html
	${HACHA} $R.html

bib:
	${BIB} $R

clean:
	rm *.log *.aux *.out *.pdf *.bbl *.blg *.toc *.html *.haux *.class *.css *backup *.htoc

