# isaweb makefile - project-specific dependencies
# $Id$

DEP_SYMLINKS=$(OUTPUTROOT)/dist/packages

$(DEP_SYMLINKS): $(ISABELLE_DIST)
	mkdir -p $(OUTPUTROOT)/dist
	ln -s $< $@

include/documentationdist.include.html: $(ISABELLE_DOC_CONTENT_FILE)
	perl build/mkcontents.pl -p '//dist/packages/Isabelle/doc/' $< $@