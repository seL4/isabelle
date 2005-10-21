# isaweb makefile - project-specific dependencies
# $Id$

include conf/distinfo.mak
conf/distinfo.mak:
	@echo 'There is no $@ file; it should have been allocated by makedist.'; \
	@echo 'If you have no makedist at hand, check out default $@ from CVS'; \
	@false; \

project: $(OUTPUTROOT)/dist site
.PHONY: project

cleanproject:
	rm -rf $(OUTPUTROOT)/dist
.PHONY: cleanproject

ifeq ($(RSYNC),)

$(OUTPUTROOT)/dist: $(ISABELLE_DIST)
	mkdir -p $@
	$(COPY) -vRud $</[^w]* $@
	chgrp -R $(TARGET_GROUP) $@
	chmod -R u-w,g-w,o-w $@
	-[ ! -e Isabelle ] && ln -s $(ISABELLE_DIST)/$(DISTNAME) Isabelle
	-chgrp -h $(TARGET_GROUP) Isabelle
	-chmod -h u-w,g-w,o-w Isabelle

else

$(OUTPUTROOT)/dist: $(ISABELLE_DIST) SYNC_ALWAYS
	mkdir -p $@
	$(RSYNC) -v --exclude='/website/' -a --delete --delete-after $</ $@
	chgrp -R $(TARGET_GROUP) $@
	chmod -R u-w,g-w,o-w $@
	-[ ! -e Isabelle ] && ln -s $(ISABELLE_DIST)/$(DISTNAME) Isabelle
	-chgrp -h $(TARGET_GROUP) Isabelle
	-chmod -h u-w,g-w,o-w Isabelle

SYNC_ALWAYS:

endif

include/documentationdist.include.html: $(ISABELLE_DOC_CONTENT_FILE)
	perl build/mkcontents.pl -p '//dist/Isabelle/doc/' $< $@

perms:
	build/set_perm.bash $(FIND) $(LOCAL_UMASK_FILE) $(LOCAL_UMASK_DIR) $(LOCAL_GROUP)
.PHONY: perms