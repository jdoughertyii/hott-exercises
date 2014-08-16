TEXDIR = tex
CHAPS = $(wildcard chap*.v)
TCHAPS = $(CHAPS:%.v=tex/%.tex)

all: pdf

pdf: $(TCHAPS)
	cd $(TEXDIR) ; make hott-exercises ; mv -f hott-exercises.pdf ..

tex/%.tex : %.v %.glob
	coqdoc --interpolate --latex --body-only -s -d tex $<
	mv $*.glob src
	cp {src,tex}/coqdoc.sty

%.glob : %.v
	hoqc $<

clean:
	rm -f src/*.glob
	rm -f *.vo
	rm -f tex/chap*.tex
	cd $(TEXDIR) ; make clean
