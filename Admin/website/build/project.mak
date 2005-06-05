# isaweb makefile - project-specific dependencies
# $Id$

symlinks: $(DEP_SYMLINKS)
.PHONY: symlinks

#~ DEP_SYMLINKS=$(OUTPUTROOT)/dist/packages $(OUTPUTROOT)/library

#~ $(OUTPUTROOT)/dist/packages: $(ISABELLE_DIST)
	#~ mkdir -p $(OUTPUTROOT)/dist
	#~ ln -s $< $@

#~ $(OUTPUTROOT)/library: $(ISABELLE_LIBR)
	#~ ln -s $< $@

DEP_SYMLINKS=dist/packages library

dist/packages: $(ISABELLE_DIST)
	ln -s $< $@

library: $(ISABELLE_LIBR)
	ln -s $< $@

include/documentationdist.include.html: $(ISABELLE_DOC_CONTENT_FILE)
	perl build/mkcontents.pl -p '//dist/packages/Isabelle/doc/' $< $@