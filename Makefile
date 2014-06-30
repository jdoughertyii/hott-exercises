TEXDIR = tex

all: doc

doc: pdf

pdf: tex/chap01.tex
	cd $(TEXDIR) ; make hott-exercises ; mv -f hott-exercises.pdf ..

tex/chap01.tex : chap01.glob
	coqdoc --interpolate --latex --body-only -l -s -d tex \
		chap01.v
	cp {src,tex}/coqdoc.sty

chap01.glob : chap01.v
	hoqc chap01.v

clean:
	rm -f tex/chap01.tex
	rm -f chap01.vo
	rm -f chap01.glob
	cd $(TEXDIR) ; make clean

#all: sources pdf
#
#$(f.tex): %.tex: %.nw
#	noweave -delay -filter \
#		  $(TEXDIR)/pygnoweb.py $< \
#		| sed -e 's/\\\\PY/\\PY/g' \
#		| sed -e 's/\\}/}/g' \
#		| sed -e 's/\\{/{/g' \
#		| sed -e 's/\\PYZhy{}\\PYZgt{}/\\mLA\\ensuremath{\\rightarrow}\\mRA/g' \
#		| sed -e 's/\\PYZlt{}\\PYZhy{}/\\mLA\\ensuremath{\\leftarrow}\\mRA/g' \
#		| sed -e 's/\\PYZlt{}\\PYZhy{}\\PYZgt{}/\\mLA\\ensuremath{\\leftrightarrow}\\mRA/g' \
#		| sed -e 's/=\\PYZgt{}/\\mLA\\ensuremath{\\Rightarrow}\\mRA/g' \
#		> $(TEXDIR)/$@
##    do cartesian product, \forall, and \exists
##    {<==}{{$\leq\;$}}1
##    {\\o}{{$\circ\;$}}1 
##    {\/\\}{{$\wedge\;$}}1
##    {\\\/}{{$\vee\;$}}1
##    {++}{{\code{++}}}1
##    {\@\@}{{$@$}}1
##    {\\mapsto}{{$\mapsto\;$}}1
##    {\\hline}{{\rule{\linewidth}{0.5pt}}}1
#
#pdf: $(f.tex)
#	cd $(TEXDIR); make hott-exercises; mv hott-exercises.pdf ..; cd $(srcdir)
#
#
#sources: $(f.v)
#
#$(f.v): %.v: %.nw
#	notangle -R$@ $< > $(VDIR)/$@
#
#clean:
#	rm -f $(VDIR)/$(f.v)
#	rm -f $(TEXDIR)/$(f.tex)
#	cd $(TEXDIR); make clean; cd $(srcdir)
