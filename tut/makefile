MAKEFLAGS += -j

all: ne.html or.html

ne.html: ne.md ty.bib ../k/pizarnik.xml
	pandoc ne.md --bibliography ty.bib -s --syntax-definition=../k/pizarnik.xml -o $@

or.html: or.md ty.bib ../k/pizarnik.xml
	pandoc or.md --bibliography ty.bib -s --mathjax --syntax-definition=../k/pizarnik.xml -o $@

clean:
	rm -rf *.html
