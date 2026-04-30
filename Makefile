all: hott std
.PHONY: all

hott:
	rm -f _CoqProject
	ln -s hott/_CoqProject _CoqProject
	$(MAKE) -C hott all
.PHONY: hott

install-hott: hott
	$(MAKE) -C hott install
.PHONY: install-hott


std:
	rm -f _CoqProject
	ln -s std/_CoqProject _CoqProject
	$(MAKE) -C std all
.PHONY: std

install-std: std
	$(MAKE) -C std install
.PHONY: install-std


test-std: std
	rm -f tests/_CoqProject
	ln -sr tests/_CoqProject.std tests/_CoqProject
	$(MAKE) COQPROJECTFILE=./_CoqProject.std -C tests all
.PHONY: test-std

test-hott: hott
	rm -f tests/_CoqProject
	ln -sr tests/_CoqProject.hott tests/_CoqProject
	$(MAKE) COQPROJECTFILE=./_CoqProject.hott -C tests all
.PHONY: test-hott

clean:
	$(MAKE) -C hott clean
	$(MAKE) -C std clean
	$(MAKE) COQPROJECTFILE=./_CoqProject.std  -C tests clean
	$(MAKE) COQPROJECTFILE=./_CoqProject.hott -C tests clean
.PHONY: clean
