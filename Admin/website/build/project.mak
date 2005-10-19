# isaweb makefile - project-specific dependencies
# $Id$

project: $(OUTPUTROOT)/dist site
.PHONY: project

cleanproject:
	rm -rf $(OUTPUTROOT)/dist
.PHONY: cleanproject

ifeq ($(RSYNC),)

$(OUTPUTROOT)/dist: $(ISABELLE_DIST)
	mkdir -p $@
	$(COPY) -vRud $< $@
	chmod -R g-w $@

else

$(OUTPUTROOT)/dist: $(ISABELLE_DIST) SYNC_ALWAYS
	mkdir -p $@
	$(RSYNC) -v -a --delete --delete-after $</ $@
	chmod -R g-w $@

SYNC_ALWAYS:

endif

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

perms:
	build/set_perm.bash $(FIND) $(LOCAL_UMASK_FILE) $(LOCAL_UMASK_DIR) $(LOCAL_GROUP)
.PHONY: perms