all: build
.PHONY: all

build: theory mllib
.PHONY: build

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

theory: CoqMakefile
	+@make -f CoqMakefile
.PHONY: theory

test:
	cd test
	npm run test
.PHONY: test

mllib: theory
	dune build
.PHONY: mllib

clean-extraction:
	dune clean
	find src/extraction/. -type f -name "*.ml" -delete
	find src/extraction/. -type f -name "*.mli" -delete

clean: CoqMakefile
	+@make -f CoqMakefile clean
	rm -f CoqMakefile
	dune clean
	find src/extraction/. -type f -name "*.ml" -delete
	find src/extraction/. -type f -name "*.mli" -delete
.PHONY: clean

install: build
	dune install
.PHONY: install

uninstall:
	dune uninstall
.PHONY: uninstall

# Forward most things to Coq makefile. Use 'force' to make this phony.
%: CoqMakefile force
	+@make -f CoqMakefile $@
force: ;
all: theory

# Do not forward these files
Makefile _CoqProject: ;
