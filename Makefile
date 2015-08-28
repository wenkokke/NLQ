default:
	./buildfile.hs

clean:
	./buildfile.hs clobber
	find . -name "*.agdai" -exec rm {} \;

listings:
	./buildfile.hs listings

.phony: clean listings
