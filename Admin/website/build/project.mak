# isaweb makefile - project-specific dependencies
# $Id$

#~ DEP_SYMLINKS=$(OUTPUTROOT)/dist/packages $(OUTPUTROOT)/library

#~ $(OUTPUTROOT)/dist/packages: $(ISABELLE_DIST)
	#~ mkdir -p $(OUTPUTROOT)/dist
	#~ ln -s $< $@

DEP_SYMLINKS=dist/packages $(OUTPUTROOT)/library

dist/packages: $(ISABELLE_DIST)
	ln -s $< $@

#~ library: $(ISABELLE_LIBR)
#~	ln -s $< $@

$(OUTPUTROOT)/library: $(ISABELLE_LIBR)
	ln -s $< $@

include/documentationdist.include.html: $(ISABELLE_DOC_CONTENT_FILE)
	perl build/mkcontents.pl -p '//dist/packages/Isabelle/doc/' $< $@

symlinks: $(DEP_SYMLINKS)
.PHONY: symlinks
