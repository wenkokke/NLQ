MARKDOWN_UNLIT := $(shell which markdown-unlit 2>/dev/null)

default: README
	@./README

README: README.lhs
ifndef MARKDOWN_UNLIT
	cabal install markdown-unlit
endif
	ghc -pgmL markdown-unlit --make README

.PHONY: clean clobber

clean:
	@find . -name "*.hi" -or -name "*.o" -or -name "*.dyn_hi" \
            -or -name "*.dyn_o" -or -name "*.agdai" | xargs rm

clobber: clean
	@rm -f "README"
