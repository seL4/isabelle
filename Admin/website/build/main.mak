# isaweb makefile
# $Id$

# force shell
SHELL=bash

# some global variables
CONF=conf/localconf.mak

# configuration switch
ifeq ($(phase), init)

# allocate configuration
init:
	mkdir -p conf
	case $$HOSTNAME in sunbroy*) ARCH=sun;; *) ARCH=at;; esac; \
	sed 's/# $$Id.*//g' build/localconf.$$ARCH.template.mak > $(CONF)
	$$EDITOR $(CONF)
	@false
.PHONY: init

else

# default target
default: project

# check configuration
include $(CONF)
$(CONF):
	@if [ ! -e $(CONF) ]; \
	then \
		echo 'Framework not configured yet; set EDITOR environment variable'; \
		echo 'to your favorite editor and type'; \
		echo; \
		echo '    make phase=init'; \
		echo; \
		echo 'to configure it'; \
		false; \
	else \
		:; \
	fi

# tidy handling
ifeq ($(DISABLE_TIDY),)
TIDYCMD=$(TIDY) -q -i -asxhtml --output-xhtml true \
                --doctype auto \
                --literal-attributes true \
                --wrap 0 \
                --indent auto --indent-spaces 2 \
                --input-encoding utf8 --output-encoding latin1 \
                --logical-emphasis yes --gnu-emacs yes --write-back yes
else
TIDYCMD=:
endif

# dependencies
DEP_FILE=conf/depends.mak
site: $(DEP_FILE) allsite
.PHONY: site

# import dependencies
include $(DEP_FILE)
endif

# pypager iso-8859-1 hack
ifneq ($(FORCE_ISO_8859_1),)
FORCE_ENC_CMD=--encodinghtml "iso-8859-1"
else
FORCE_ENC_CMD=
endif

# import project-specific dependencies
include build/project.mak

# build dependencies
$(DEP_FILE): $(CONF)
	rm -f $(DEP_FILE); \
	touch $(DEP_FILE); \
	echo '# This is a generated file; do not edit' >> $(DEP_FILE); \
	echo >> $(DEP_FILE); \
	allstatic=''; \
	for dir in $(STATICDIRS); \
	do \
		for file in `$(FIND) $$dir -follow -type f -a ! -path "*/CVS/*"`; \
		do \
			outputfile=$(OUTPUTROOT)/$$file; \
			outputdir=`dirname $$outputfile`; \
			echo "$$outputfile: $$file" >> $(DEP_FILE); \
			echo "	mkdir -p $$outputdir" >> $(DEP_FILE); \
			echo "	-chmod $(TARGET_UMASK_DIR) $$outputdir" >> $(DEP_FILE); \
			echo '	cp $$< $$@' >> $(DEP_FILE); \
			echo '	chmod $(TARGET_UMASK_FILE) $$@' >> $(DEP_FILE); \
			allstatic="$$allstatic$$outputfile "; \
			echo >> $(DEP_FILE); \
		done; \
	done; \
	echo "DEP_ALLSTATIC=$$allstatic" >> $(DEP_FILE); \
	echo >> $(DEP_FILE); \
	echo 'DEP_HTML=$$(DEP_ALLSTATIC) $$(DEP_SYMLINKS) include/documentationdist.include.html $(DEP_FILE) $(CONF)' >> $(DEP_FILE); \
	echo >> $(DEP_FILE); \
	allhtml=''; \
	for html in `$(FIND) . -name "*.html" -a ! -name "*.include.html"`; \
	do \
		outputfile=$(OUTPUTROOT)/$$html; \
		outputdir=`dirname $$outputfile`; \
		echo "$$outputfile: $$html"' $$(DEP_HTML)' >> $(DEP_FILE); \
		echo "	mkdir -p $$outputdir" >> $(DEP_FILE); \
		echo "	-chmod $(TARGET_UMASK_DIR) $$outputdir" >> $(DEP_FILE); \
		echo '	$(PYTHON) build/pypager.py --dtd="dtd/" $(FORCE_ENC_CMD) --srcroot="." --dstroot="$(OUTPUTROOT)" --spamprotect distname="$(DISTNAME)" $$< $$@' >> $(DEP_FILE); \
		echo '	-$(TIDYCMD) $$@' >> $(DEP_FILE); \
		echo '	chmod $(TARGET_UMASK_FILE) $$@' >> $(DEP_FILE); \
		allhtml="$$allhtml$$outputfile "; \
		echo >> $(DEP_FILE); \
	done; \
	echo "DEP_ALLHTML=$$allhtml" >> $(DEP_FILE); \
	echo >> $(DEP_FILE); \
	echo 'allsite: $$(DEP_ALLHTML) $$(DEP_ALLSTATIC)' >> $(DEP_FILE); \
	echo ".PHONY: allsite" >> $(DEP_FILE)

# build dependencies explicitly
depends:
	rm -f $(DEP_FILE)
	$(MAKE) $(DEP_FILE)
.PHONY: depends

# clean build files
clean:
	rm -f $(DEP_FILE)
.PHONY: clean
