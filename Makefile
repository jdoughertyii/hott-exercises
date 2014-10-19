TEXDIR = tex
CHAPS = $(wildcard Ch*.v)
TCHAPS = $(CHAPS:%.v=tex/%.tex)

all: pdf

pdf: $(TCHAPS)
	cd $(TEXDIR) ; make hott-exercises ; mv -f hott-exercises.pdf ..

tex/%.tex : %.v %.glob
#	coqdoc --latex -s --body-only -d tex --interpolate --parse-comments $<
	cp {src,tex}/coqdoc.sty

%.glob : %.v
	hoqc $<

clean:
	rm -f *.glob
	rm -f *.vo
	rm -f tex/Ch*.tex
	cd $(TEXDIR) ; make clean
