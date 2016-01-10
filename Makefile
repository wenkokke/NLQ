MAKEFLAGS=B

default:
	./buildfile.hs

%:
	./buildfile.hs $@
