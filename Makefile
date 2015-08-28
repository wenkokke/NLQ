default:
	./buildfile.hs

clean:
	./buildfile.hs clobber


listings:
	./buildfile.hs listings

.phony: clean listings
