# isaweb makefile - project-specific dependencies
# $Id$

project: $(OUTPUTROOT)/dist site
.PHONY: project

cleanproject:
	rm -rf $(OUTPUTROOT)/dist
.PHONY: cleanproject

$(OUTPUTROOT)/dist: $(ISABELLE_DIST)
	$(COPY) -vRud $< $@
	chmod -R g-w $@

include/documentationdist.include.html: $(ISABELLE_DOC_CONTENT_FILE)
	perl build/mkcontents.pl -p '//dist/Isabelle/doc/' $< $@

include conf/distname.mak
conf/distname.mak:
	@echo 'There is no conf/distname.mak file; it should have been'; \
	echo 'allocated by makedist.'; \
	echo 'If you have no makedist at hand, allocate a conf/distname.mak file'; \
	echo 'yourself, e. g. by:'; \
	echo; \
	echo 'echo "DISTNAME=Isabelle1705" > conf/distname.mak'; \
	echo; \
	false; \
