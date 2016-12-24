# Makefile for printing oyster document.

LATEX=pdflatex
CC=gcc

oyster.pdf: oyster.tex oyster.ind
	${LATEX} oyster.tex ;

oyster.tex: oyster.pl protex
	./Pro2TeX oyster

oyster.ind: oyster.idx
	makeindex -c oyster

oyster.idx: oyster.tex
	latex oyster.tex

# version without docs.
oyster.raw: oyster.pl
	egrep '^[^%]' oyster.pl > oyster.raw
protex: protex.c
	${CC} -O -o protex protex.c

clean:
#	rm -f oyster.pl
	rm -f oyster.tex
	rm -f *.aux *.bbl *.blg *.dvi *.log *.toc *.ind *.idx *.inx \
           *.glo *.lof *.lot *.srt protex *~ \#*\# *.ilg
