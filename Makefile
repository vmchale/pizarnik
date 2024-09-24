MAKEFLAGS += --no-builtin-rules -j
.DELETE_ON_ERROR:

HS_SRC = $(shell fd '\.(hs|x|y|hsc|cpphs)$$' $$(ja -F'\s*:\s*' '{%/hs-source-dirs/}{`2}' -i pizarnik.cabal))

moddeps.svg: $(HS_SRC)
	graphmod -i src | dot -Tsvg -o $@

clean:
	make -C tex
	rm -rf dist-newstyle tags tags.mtime moddeps.svg

install:
	cabal install

fmt:
	fd '\.(cpphs|hs)$$' $$(ja -F'\s*:\s*' '{%/hs-source-dirs/}{`2}' -i pizarnik.cabal) -x stylish-haskell -i

fix: $(HS_SRC)
	fd '\.(cpphs|hs|x|y|hsc)$$' $$(ja -F'\s*:\s*' '{%/hs-source-dirs/}{`2}' -i pizarnik.cabal) -x ja "{%/^\s*infix(r|l)?\s+\d+/}{sprintf '- fixity: %s' \`0}}" -i

tags: $(HS_SRC)
	rm -f tags
	ghc-tags --ctags
	ctags --append=yes --languages=ALEX,HAPPY -R src
