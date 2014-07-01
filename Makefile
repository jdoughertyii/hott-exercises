TEXDIR = tex
CHAPS = $(wildcard chap*.v)
TCHAPS = $(CHAPS:%.v=tex/%.tex)

all: pdf

pdf: $(TCHAPS)
	cd $(TEXDIR) ; make hott-exercises ; mv -f hott-exercises.pdf ..

tex/%.tex : %.v %.glob
	coqdoc --interpolate --latex --body-only -s -d tex $<
	mv $*.glob src
	mv $*.vo src
	cp {src,tex}/coqdoc.sty

%.glob : %.v
	hoqc $<

clean:
	rm -f src/*.glob
	rm -f src/*.vo
	rm -f tex/chap*.tex
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
