MAKEFLAGS += -j

all: ne.html or.html perm.html inv.html

PANDOC_FLAGS := -s --citeproc --bibliography ty.bib --syntax-definition=../pandoc/pizarnik.xml

ne.html: ne.md ty.bib ../pandoc/pizarnik.xml ../lib/list.piz
	pandoc ne.md --lua-filter=include-code-files.lua $(PANDOC_FLAGS) -o $@

inv.html: inv.md ty.bib ../pandoc/pizarnik.xml ../lib/maybe.piz
	pandoc inv.md --lua-filter=include-code-files.lua --mathjax $(PANDOC_FLAGS) -o $@

or.html: or.md ../pandoc/pizarnik.xml
	pandoc or.md --mathjax $(PANDOC_FLAGS) -o $@

perm.html: perm.md ty.bib ../pandoc/pizarnik.xml
	pandoc perm.md $(PANDOC_FLAGS) -o $@

clean:
	rm -rf *.html
