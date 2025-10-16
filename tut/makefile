ne.html: ne.md ty.bib ../k/pizarnik.xml
	pandoc ne.md --bibliography ty.bib -s --syntax-definition=../k/pizarnik.xml -o $@

clean:
	rm -rf *.html
