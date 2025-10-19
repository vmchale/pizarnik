MAKEFLAGS += -j

all: ne.html or.html

ne.html: ne.md ty.bib ../pandoc/pizarnik.xml
	pandoc ne.md --bibliography ty.bib -s --syntax-definition=../pandoc/pizarnik.xml -o $@

or.html: or.md ty.bib ../pandoc/pizarnik.xml
	pandoc or.md --bibliography ty.bib -s --mathjax --syntax-definition=../pandoc/pizarnik.xml -o $@

clean:
	rm -rf *.html
