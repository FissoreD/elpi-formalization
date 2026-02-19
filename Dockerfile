FROM ocaml/opam:debian-13-opam

RUN sudo apt-get install linux-libc-dev pkg-config libgmp-dev --yes
RUN opam switch create default ocaml-base-compiler.5.1.1
RUN eval $(opam env)
RUN opam install rocq-core.9.0.0 --yes

RUN opam repo add --all rocq https://rocq-prover.org/opam/released
RUN opam install rocq-mathcomp-ssreflect.2.4.0 rocq-stdlib --yes
RUN eval $(opam env --root=./_opam)

WORKDIR /root/blah/
COPY . .
# RUN rocq makefile -f _CoqProject -o Makefile
# docker run --user root -it opam /bin/bash
