MAKEFLAGS=B
DELEGATE=./buildfile.hs

default:
	@$(DELEGATE)

%:
	@$(DELEGATE) $@
