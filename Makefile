MAKEFLAGS=B
DELEGATE=./buildfile.hs

default:
	@ghc --make $(DELEGATE) -rtsopts -with-rtsopts=-I0 -outputdir=_build -o _build/build
	@_build/build

%:
	@ghc --make $(DELEGATE) -rtsopts -with-rtsopts=-I0 -outputdir=_build -o _build/build
	@_build/build "$@"
