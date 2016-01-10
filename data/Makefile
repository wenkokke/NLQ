MARKDOWN_UNLIT := $(shell which markdown-unlit 2>/dev/null)
SOURCES := $(wildcard *.hs)

default: README
	@./README


.PHONY: README
README:
	@rm -f "README"
ifndef MARKDOWN_UNLIT
	cabal install markdown-unlit
endif
	@ghc -pgmL markdown-unlit --make README


.PHONY: clean
clean:
	@find . -name "*.hi" -or -name "*.o" -or -name "*.dyn_hi" \
            -or -name "*.dyn_o" -or -name "*.agdai" | xargs rm
	@rm -f "Makefile.bak"


.PHONY: clobber
clobber: clean
	@rm -f "README"


.PHONY: update-deps
update-deps:
	@ghc -pgmL markdown-unlit -M README.lhs -dep-suffix "" -dep-suffix "dyn_"
