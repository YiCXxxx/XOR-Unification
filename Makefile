# Coq project makefile
# John D. Ramsdell (the MITRE Corporation)
# tiny tweaks by Dan Dougherty, WPI

# Documentation target. 
# Type "make DOC=gallinahtml" to make HTML without proofs.
# Type "make DOC=html" to make HTML with proofs.
# Type "make DOC=all-gal.pdf" to make PDF without proofs.
# Type "make DOC=all.pdf" to make PDF with proofs.


# default form of doc if you just type make
# DOC	?= all-gal.pdf
# DOC	?= gallinahtml
DOC	?= html         # html with proofs

# File $(PROJ) contains the list of source files.
# See "man coq_makefile" for its format.
PROJ	= _CoqProject

# Generated makefile
COQMK	= coq.mk

all:	$(COQMK)
	$(MAKE) -f $(COQMK)
	$(MAKE) -f $(COQMK) $(DOC)

$(COQMK): $(PROJ)
	coq_makefile -o $(COQMK) -f $(PROJ)

$(PROJ):
	@echo make $@

%:	$(COQMK) force
	$(MAKE) -f $(COQMK) $@

clean:	$(COQMK)
	$(MAKE) -f $(COQMK) clean
	rm $(COQMK)

.PHONY:	all clean force
