all: theory patch mllib
.PHONY: all

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

theory: CoqMakefile
	+@make -f CoqMakefile
.PHONY: theory

clean: CoqMakefile
	+@make -f CoqMakefile clean
	rm -f CoqMakefile
	dune clean
	find src/. -type f -name "*.ml" -delete
	find src/. -type f -name "*.mli" -delete
	find src2/. -type f -name "*.ml" -delete
	find src2/. -type f -name "*.mli" -delete
.PHONY: clean

install: CoqMakefile
	+@make -f CoqMakefile install
.PHONY: install

uninstall: CoqMakefile
	+@make -f CoqMakefile uninstall
.PHONY: uninstall

patch: theory
	patch -p1 < patches/int.diff
	patch -p1 < patches/misc.diff
.PHONY: patch

mllib: patch
	dune build
.PHONY: mllib

# Forward most things to Coq makefile. Use 'force' to make this phony.
%: CoqMakefile force
	+@make -f CoqMakefile $@
force: ;
all: theory

# Do not forward these files
Makefile _CoqProject: ;
