AGDA=agda

.PHONY: listings
listings: src/Everything.agda
	$(AGDA) -isrc -i$(AGDA_HOME) --html src/Everything.agda -v0

.PHONY: src/Everything.agda
src/Everything.agda: $(find src -name '*.agda')
	rm -f src/Everything.agda
	runhaskell GenerateEverything.hs
