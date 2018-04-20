install:
	mkdir -p bin
	stack install --local-bin-path=bin --copy-bins --profile

setup:
	stack setup

clean:
	stack clean

bindir = bin

cabal-install: cabal-build
	cabal install --bindir=$(bindir)
	@echo ""
	@echo "Make sure to add bin/ to PATH, if desired."

cabal-build: cabal-configure
	cabal build

cabal-configure:
	cabal configure

cabal-clean:
	cabal clean
