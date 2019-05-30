all: default

default: Makefile.coq infotheo/Makefile
	$(MAKE) -f Makefile.coq
	$(MAKE) -C infotheo -f Makefile

install: Makefile.coq infotheo/Makefile
	$(MAKE) -f Makefile.coq install
	$(MAKE) -C infotheo -f Makefile install

clean: Makefile.coq infotheo/Makefile
	$(MAKE) -f Makefile.coq cleanall
	$(MAKE) -C infotheo -f Makefile cleanall
	rm -f Makefile.coq Makefile.coq.conf
	rm -f infotheo/Makefile infotheo/Makefile.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
	echo " " >> Makefile.coq
	echo "infotheo/%.vio: " >> Makefile.coq
	echo "	$(MAKE) -C infotheo -f Makefile quick" >> Makefile.coq
	echo "infotheo/%.vo: " >> Makefile.coq
	echo "	$(MAKE) -C infotheo -f Makefile quick" >> Makefile.coq

infotheo/Makefile: infotheo/_CoqProject
	cd infotheo && coq_makefile -f _CoqProject -o Makefile

infotheo/_CoqProject:
	git submodule update --recursive --init .

.PHONY: all default quick install clean
