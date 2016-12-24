# Makefile for Clam manual
# @(#)$Id: Makefile,v 1.10 2013/02/20 15:48:41 smaill Exp $
# $Log: Makefile,v $
# Revision 1.10  2013/02/20 15:48:41  smaill
# switch latex to pdflatex and produce pdf
#
# Revision 1.9  2013/02/20 15:35:34  smaill
# testing
#
# Revision 1.8  1999/02/24 15:36:44  img
# *** empty log message ***
#
# Revision 1.7  1997/10/16 11:13:46  img
# *** empty log message ***
#
# Revision 1.6  1997/09/26 14:33:19  img
# update
#
# Revision 1.5  1996/07/10 14:34:20  img
# *** empty log message ***
#
# Revision 1.4  1996/07/02 14:21:59  img
# Updates for Clam 2.5;  alterations for LaTeX2e
#
# Revision 1.3  1995/10/03  12:46:45  img
# Updates for Clam 2.4
#
# Revision 1.2  1995/04/26  16:12:26  img
# 	* sh sortindex to avoid PATH problem
#
# Revision 1.1  1994/09/16  09:23:51  dream
# Initial revision
#

.SUFFIXES : .tex .pdf

manual.dvi : Titlepage.tex Introduction.tex manual.tex ProgrammerManual.tex \
	      UserManual.tex appendix.tex general.tex \
	      proof-planning.tex header.tex footer.tex tactics_util.tex \
	      clam-manual.sty
	pdflatex manual.tex
	bibtex manual
	pdflatex manual
	bibtex manual
	pdflatex manual.tex
	make indices
	pdflatex manual
indices:
	makeindex -s manual.ist -o manual.ind manual.idx
	makeindex -s manual.ist -o manual.pred-ind manual.pred-idx
	makeindex -s manual.ist -o manual.mthd-ind manual.mthd-idx
	makeindex -s manual.ist -o manual.file-ind manual.file-idx

methods:
	sh make_mthds

clean :
	rm -f *.aux *.bbl *.blg *.dvi *.log *.toc *.ind *.idx *.inx \
              *.glo *.lof *.lot *.srt *.pred* *~ \
		*.*-idx *.*-ind *.bak *.ilg
