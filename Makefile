MAKEFLAGS=B
DELEGATE=./buildfile.hs

default:
	@$(DELEGATE)

%:
	@$(DELEGATE) $@


# ghc --make buildfile.hs -rtsopts -with-rtsopts=-I0 -outputdir=_build -o _build/build && _build/build "$@"
