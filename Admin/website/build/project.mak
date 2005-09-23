# isaweb makefile - project-specific dependencies
# $Id$

project: site
	chmod -R g-w $(OUTPUTROOT)/dist/packages
.PHONY: project

#~ DEP_SYMLINKS=$(OUTPUTROOT)/dist/packages $(OUTPUTROOT)/library

#~ $(OUTPUTROOT)/dist/packages: $(ISABELLE_DIST)
	#~ mkdir -p $(OUTPUTROOT)/dist
	#~ ln -s $< $@

DEP_SYMLINKS=dist/packages $(OUTPUTROOT)/dist/library

dist/packages: $(ISABELLE_DIST)
	mkdir -p dist
	ln -s $< $@

#~ library: $(ISABELLE_LIBR)
#~	ln -s $< $@

$(OUTPUTROOT)/dist/library: $(ISABELLE_LIBR)
	mkdir -p $(OUTPUTROOT)/dist
	ln -s $< $@
	chmod $(TARGET_UMASK_DIR) $@

include/documentationdist.include.html: $(ISABELLE_DOC_CONTENT_FILE)
	perl build/mkcontents.pl -p '//dist/packages/Isabelle/doc/' $< $@

symlinks: $(DEP_SYMLINKS)
.PHONY: symlinks

include conf/distname.mak
conf/distname.mak:
	@echo 'There is no conf/distname.mak file; it should have been'; \
	echo 'allocated by makedist.'; \
	echo 'If you have no makedist at hand, allocate a conf/distname.mak file'; \
	echo 'yourself, e. g. by:'; \
	echo; \
	echo 'echo "DISTNAME=Isabelle2004" > conf/distname.mak'; \
	echo; \
	false; \
