# This prevents Coq from producing stack backtraces.
export OCAMLRUNPARAM=
# The name of the package.
NAME=coq-iteration

.PHONY: all
all:
	@ dune build --display=short

.PHONY: clean
clean:
	@ git clean -fdX .

.PHONY: lint
lint:
	@ dune build $(NAME).opam
	@ opam lint $(NAME).opam

# [make axioms] looks for suspicious keywords in the Coq sources.

.PHONY: axioms
axioms:
	@ for word in Axiom Abort Admitted ; do \
	    git grep $${word} '*.v' || true ; \
	  done
