# isaweb makefile - project-specific dependencies
# $Id$

include conf/distinfo.mak
conf/distinfo.mak:
	@echo 'There is no $@ file; it should have been allocated by makedist.'; \
	@echo 'If you have no makedist at hand, check out default $@ from CVS'; \
	@false; \

STATICDIRS=css img media misc js
STATICFILES=include/documentationdist.include.html
OUTPUTDIST_REL=dist-$(DISTNAME)
OUTPUTDIST=$(OUTPUTROOT)/$(OUTPUTDIST_REL)

project: $(OUTPUTDIST) site
.PHONY: project

cleanproject:
	rm -rf $(OUTPUTDIST)
.PHONY: cleanproject

ifeq ($(RSYNC),)

$(OUTPUTDIST): $(ISABELLE_DIST)
	mkdir -p $@
	$(COPY) -vRud $</[^w]* $@
	-chgrp -hR $(TARGET_GROUP) $@
	-chmod -R u+w,g-w,o-w $@
	rm -f $@/Isabelle && ln -s $(ISABELLE_DIST)/$(DISTNAME) $@/Isabelle
	-chgrp -h $(TARGET_GROUP) $@/Isabelle
	-chmod u+w,g-w,o-w $@/Isabelle
	( cd $(OUTPUTROOT) && rm -f dist && ln -s $(OUTPUTDIST_REL) dist)

else

$(OUTPUTDIST): $(ISABELLE_DIST) SYNC_ALWAYS
	mkdir -p $@
	$(RSYNC) -v --exclude='/website/' -rlt --delete --delete-after $</ $@
	-chgrp -hR $(TARGET_GROUP) $@
	-chmod -R u+w,g-w,o-w $@
	rm -f $@/Isabelle &&  ln -s $(ISABELLE_DIST)/$(DISTNAME) $@/Isabelle
	-chgrp -h $(TARGET_GROUP) $@/Isabelle
	-chmod u+w,g-w,o-w $@/Isabelle
	( cd $(OUTPUTROOT) && rm -f dist && ln -s $(OUTPUTDIST_REL) dist)

SYNC_ALWAYS:

endif

include/documentationdist.include.html: $(ISABELLE_DOC_CONTENT_FILE)
	perl build/mkcontents.pl -p '//dist/Isabelle/doc/' $< $@

perms:
	build/set_perm.bash $(FIND) $(LOCAL_UMASK_FILE) $(LOCAL_UMASK_DIR) $(LOCAL_GROUP)
.PHONY: perms