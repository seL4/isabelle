# isaweb makefile - project-specific dependencies
# $Id$

DEP_SYMLINKS=$(OUTPUTROOT)/dist/packages $(OUTPUTROOT)/library

$(OUTPUTROOT)/dist/packages: $(ISABELLE_DIST)
	mkdir -p $(OUTPUTROOT)/dist
	ln -s $< $@

$(OUTPUTROOT)/library:
	ln -s $< $@

include/documentationdist.include.html: $(ISABELLE_DOC_CONTENT_FILE)
	perl build/mkcontents.pl -p '//dist/packages/Isabelle/doc/' $< $@