all: coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq src/Compiler.v src/Proofs.v
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

clean:
	rm -f src/*.vo src/*.glob src/*.v.d Makefile.coq
