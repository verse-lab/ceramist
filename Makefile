all: default

default: Makefile.coq 
	$(MAKE) -f Makefile.coq


install: Makefile.coq 
	$(MAKE) -f Makefile.coq install

doc: Makefile.coq 
	$(MAKE) -f Makefile.coq html


clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf


Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all default quick install clean
