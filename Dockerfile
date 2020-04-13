FROM ubuntu:18.04

# install opam
RUN apt-get update && \
	apt-get -y install software-properties-common && \
	add-apt-repository ppa:avsm/ppa && \
	apt update && apt -y install opam make m4 gcc git

# install coq
RUN opam init --disable-sandboxing --reinit && eval $(opam env --set-switch) && opam install -y coq


RUN opam repo add coq-released https://coq.inria.fr/opam/released && opam update && opam install -y --deps-only coq-ceramist.1.0.1

WORKDIR /ceramist/

# copy over all the files (explicit names to improve caching)
COPY Computation/*.v Computation/
COPY Structures/*.v Structures/
COPY Structures/BlockedAMQ/*.v Structures/BlockedAMQ/
COPY Structures/BloomFilter/*.v Structures/BloomFilter/
COPY Structures/Core/*.v Structures/Core/
COPY Structures/CountingBloomFilter/*.v Structures/CountingBloomFilter/
COPY Structures/QuotientFilter/*.v Structures/QuotientFilter/
COPY Utils/*.v Utils/

# Copy over the makefiles and project files
COPY CoqMakefile.local CoqMakefile.local
COPY _CoqProject _CoqProject
COPY Makefile Makefile
COPY opam opam
COPY LICENSE LICENSE
COPY project_readme.md readme.md

# build
RUN eval $(opam env) && make
