FROM ubuntu:18.04

# install opam
RUN apt-get update && \
	apt-get -y install software-properties-common && \
	add-apt-repository ppa:avsm/ppa && \
	apt update && apt -y install opam make m4 gcc git

# install coq
RUN opam init --disable-sandboxing --reinit && eval $(opam env --set-switch) && opam install -y coq


RUN opam repo add coq-released https://coq.inria.fr/opam/released && opam update && opam install -y --deps-only coq-ceramist.1.0.1

RUN git clone https://github.com/certichain/ceramist.git
WORKDIR /ceramist/
RUN eval $(opam env) && make
