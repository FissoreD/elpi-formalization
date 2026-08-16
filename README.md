# Elpi formalization — Overview

This folder contains a formalization of a logic-programming language with *cut*.
The reference concrete language is *elpi*.  We provide two operational semantics
and prove their equivalence.

The first semantics represents the execution state as a tree: internal nodes
represent disjunctions and conjunctions. Executing a *cut* node prunes specific
subtrees.

The second semantics is the *elpi* semantics. It represents the state as a list
of disjunctions, and each disjunct is a list of conjuncts. In this
representation, there is no explicit information about which alternatives should
be discarded when a cut is executed. Therefore, we annotate a cut with the set
of alternatives that must be retained after its execution.

An application of these two semantics is determinacy checking: we formalize this
classic property of logic-programming languages and prove that the static
checker guarantees that any call to deterministic predicates produces at most
one solution.

The formalization is written in the *[Rocq
Prover](https://github.com/rocq-prover/rocq)* and is located in the `./theories`
folder.

The *elpi* language is available here:
https://github.com/LPCIC/elpi

## How to build / run proofs

The mechanization requires Rocq 9.0 and mathcomp 2.4.0.
Using opam:
```
export OPAMROOT=$PWD/_opam
opam init --bare --disable-shell-hook -n
opam switch create default --packages=rocq-core.9.0.0 -y
eval $(opam env)
opam repo add --all rocq https://rocq-prover.org/opam/released
opam install rocq-mathcomp-ssreflect.2.4.0 rocq-stdlib -y
rocq makefile -f _CoqProject -o Makefile
make
```

## Disclaimer

The file finmap.v was taken from https://github.com/math-comp/finmap .
The file zify_ssreflect.v was taken from https://github.com/math-comp/mczify .

## Project structure

- **tree.v**: Formalization of the And-Or tree semantics
- **elpi.v**: Formalization of the first-order Prolog with cut semantics
- **valid_tree.v**: Definition of valid trees (SLD_tree)
- **elpi_equiv.v**: Equivalence proof between the two semantics
- **unif.v**: Formalization of Elpi unification (up to matching)
- **mgu.v**: Formalization of mgu + proof for correctness and soundess of unify
- **mut_excl.v**: Formalization of mutual exclusion checker
- **check_fo.v**: Formalization of rule checking for determinacy
- **determinacy.v**: Determinacy proof  

