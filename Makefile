.PHONY: all

all: Makefile.coq
	$(MAKE) -f Makefile.coq all

# Use the standard coq_makefile from PATH, not a rocq wrapper
COQ_MAKEFILE ?= coq_makefile

Makefile.coq:
	$(COQ_MAKEFILE) -f _CoqProject -o Makefile.coq

%:: Makefile.coq
	$(MAKE) -f Makefile.coq $@
