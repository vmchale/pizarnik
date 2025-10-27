MAKEFLAGS += -j

docs: index.html perm.html inv.html ne.html or.html

index.html: index.md
	pandoc -s $< -o $@

or.html: ../tut/or.html
	ln -f $< $@

perm.html: ../tut/perm.html
	ln -f $< $@

inv.html: ../tut/inv.html
	ln -f $< $@

ne.html: ../tut/ne.html
	ln -f $< $@
