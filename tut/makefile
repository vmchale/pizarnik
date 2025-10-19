MAKEFLAGS += -j

all: ne.html or.html perm.html

ne.html: ne.md ty.bib ../pandoc/pizarnik.xml
	pandoc ne.md --bibliography ty.bib -s --syntax-definition=../pandoc/pizarnik.xml -o $@

or.html: or.md ../pandoc/pizarnik.xml
	pandoc or.md -s --mathjax --syntax-definition=../pandoc/pizarnik.xml -o $@

perm.html: perm.md ty.bib ../pandoc/pizarnik.xml
	pandoc perm.md -s --syntax-definition=../pandoc/pizarnik.xml -o $@

clean:
clean:
	rm -rf *.html
