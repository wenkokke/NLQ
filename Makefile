MAKEFLAGS=B
DELEGATE=./buildfile.hs

default:
	@mkdir -p _build
	@ghc --make $(DELEGATE) -rtsopts -with-rtsopts=-I0 -outputdir=_build -o _build/build
	@_build/build

%:
	@mkdir -p _build
	@ghc --make $(DELEGATE) -rtsopts -with-rtsopts=-I0 -outputdir=_build -o _build/build
	@_build/build "$@"
