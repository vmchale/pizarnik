MAKEFLAGS += -j

docs: index.html

index.html: index.md perm.html inv.html ne.html or.html exp.html err.html ast.html
	pandoc -s $< -o $@

err.html: ../tut/err.html
	ln -f $< $@

or.html: ../tut/or.html
	ln -f $< $@

exp.html: ../tut/exp.html
	ln -f $< $@

perm.html: ../tut/perm.html
	ln -f $< $@

inv.html: ../tut/inv.html
	ln -f $< $@

ne.html: ../tut/ne.html
	ln -f $< $@

ast.html: ../tut/ast.html
	ln -f $< $@
