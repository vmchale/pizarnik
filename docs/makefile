MAKEFLAGS += -j

docs: index.html perm.html inv.html ne.html

index.html: index.md
	pandoc -s $< -o $@

perm.html: ../tut/perm.html
	ln -f $< $@

inv.html: ../tut/inv.html
	ln -f $< $@

ne.html: ../tut/ne.html
	ln -f $< $@
