MAKEFLAGS += -j

all: ne.html or.html perm.html inv.html exp.html err.html cat.html

PANDOC_FLAGS := -s --citeproc --lua-filter=include-code-files.lua --mathjax --syntax-definition=../pandoc/pizarnik.xml
PANDOC_FLAGS += --bibliography ty.bib

%.html: %.md ty.bib ../pandoc/pizarnik.xml
	pandoc $< $(PANDOC_FLAGS) -o $@
	# minhtml --minify-css --minify-js $@ -o $@

clean:
	rm -rf *.html
