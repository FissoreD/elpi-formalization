# Elpi formalization — Overview

This folder contains a formalization of a logic-programming language with *cut*.
The reference concrete language is *elpi*.  We provide two operational semantics
and prove their equivalence.

The first semantics represents the execution state as a tree: internal nodes
represent disjunction and conjunction.  Executing a *cut* node prunes specific
subtrees.

The second semantics is the *elpi* semantics.  It represents the state as a list
of disjunctions, and each disjunct is a list of conjuncts.  In this
representation there is no explicit information about which alternatives should
be discarded when a cut is executed.  Therefore, we annotate a cut with the set
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


<!-- ## High-level description

We provide two semantics of a 

- Purpose: briefly state what is being formalized (e.g., "a small-step semantics
  and type system for a toy language", "a verification of algorithm X", "proofs
  about data structure Y").
- Logic/assistant used: name the theorem prover or framework (e.g., Coq,
  Isabelle, Lean, Why3, custom proof engine) and any required libraries.

## Folder organization
- theories/
  - base/ — foundational definitions and common utilities (sets, lists, basic
    lemmas)
  - syntax/ — syntactic definitions (AST, tokens, parsers)
  - semantics/ — operational/denotational semantics and interpreter models
  - typing/ — typing rules, judgments, and type preservation proofs
  - properties/ — lemmas and theorems (soundness, completeness, termination)
  - proofs/ — proof scripts, automation tactics, helper lemmas
  - examples/ — example encodings and test proofs

Adjust names above to match actual subfolders in this repo.

## Notation and conventions
- Explain notation used in the theories (e.g., ⟨e,σ⟩ → ⟨e',σ'⟩ for transitions,
  Γ ⊢ e : τ for typing)
- Mention proof style (structured proofs vs tactic-based), naming conventions
  for lemmas/theorems, and file naming patterns.  -->

## How to build / run proofs

The mechanization requires Rocq 9.0 and mathcomp 2.4.0.
Using opam:
```
opam init --root ./_opam --bare
opam switch create default --packages=rocq-core.9.0.0
opam repo add --all rocq https://rocq-prover.org/opam/released
opam install rocq-mathcomp-ssreflect.2.4.0 rocq-stdlib
eval $(opam env --root=./_opam)
rocq makefile -f _CoqProject -o Makefile
make
```

sudo apt-get install linux-libc-dev pkg-config libgmp-dev --yes
opam switch create default ocaml-base-compiler.5.1.1
eval $(opam env)
opam install rocq-core.9.0.0 --yes

<!-- - Example:
  - Install dependencies: `sudo apt install coq`
  - Run full build: `make -C theories` -->


<!-- ## Key files (example)
- base/Prelude.v — base definitions and frequently used lemmas
- syntax/AST.v — AST and helpers
- semantics/SmallStep.v — small-step transition relation
- typing/Typing.v — typing judgment and typing lemmas
- properties/Progress.v — progress theorem
- properties/Preservation.v — preservation theorem

(Replace with the actual filenames in this repository.)

## Editing and extending
- How to add a new lemma: where to put it, naming conventions, and how to run
  proof checks
- How to add examples: add to examples/ and include a Makefile target if needed

## Troubleshooting
- Common build errors and remedies (version mismatches, missing stdlib packages)
- How to increase proof verbosity or use an interactive mode (REPL, proof IDE)

## References
- Links to used theorem prover docs and key papers or specs. -->