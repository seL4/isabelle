# -- makefile for Isabelle web pages (dist and main)
# -- $Id$

# --- force shell
SHELL=bash

# --- check parameters
ifeq ($(tidy),)
    TIDYCMD=:
else
    TIDYCMD=tidy -q -i -asxhtml --doctype auto --indent-spaces 2 --wrap 80 \
                --logical-emphasis yes --gnu-emacs yes --write-back yes
endif

# --- external tools

GENPAGE   = ./bin/genpage
MKCONTENT = ./bin/mkcontents

# ---
# --- genpage stuff 

# --- directories for main isabelle pages

MAIN_CONTENT = main-content
MAIN_LAYOUT  = main-layout
MAIN_TARGET  = main

# --- directories for isabelle distribution pages

DIST_CONTENT = dist-content
DIST_LAYOUT  = dist-layout
DIST_TARGET  = dist

# --- name of genpage template file
TEMPLATE_NAME = template.html

# ---
# --- doc content generation

# --- location of the Contents file of the Isabelle documentation
DOC_CONTENT_FILE = Contents

# --- target include files with documentation links
DOC_CONTENTS_MAIN = docu-contents.main
DOC_CONTENTS_DIST = docu-contents.dist

# --- target directories for publishing to web site
MAIN_PUB_MIRROR_SRC=sunbroy2.informatik.tu-muenchen.de:/home/proj/isabelle-repository/www/
MAIN_PUB_DEST=sunbroy2.informatik.tu-muenchen.de:/home/html/isabelle/html-data/
DIST_PUB_DEST=sunbroy2.informatik.tu-muenchen.de:/home/html/isabelle/html-data/dist/

# ---
# --- begin rules

all: clean main dist install weblint

main:
	@$(MKCONTENT) -p dist/`cat DISTNAME`/doc/ $(DOC_CONTENT_FILE) $(DOC_CONTENTS_MAIN)
	@env DISTNAME=`cat DISTNAME` \
	  $(GENPAGE) -t $(MAIN_LAYOUT)/$(TEMPLATE_NAME) -c $(MAIN_CONTENT) -o $(MAIN_TARGET)
	-@cd $(MAIN_TARGET); \
        for html in *.html; \
            do $(TIDYCMD) $$html; \
        done

pub-main: main
	@echo "Publishing main pages (*.html only)."
	scp main/*.html $(MAIN_PUB_MIRROR_SRC)
	scp main/*.html $(MAIN_PUB_DEST)

dist:
	@$(MKCONTENT) -p `cat DISTNAME`/doc/ $(DOC_CONTENT_FILE) $(DOC_CONTENTS_DIST)
	@env DISTNAME=`cat DISTNAME` \
	  $(GENPAGE) -t $(DIST_LAYOUT)/$(TEMPLATE_NAME) -c $(DIST_CONTENT) -o $(DIST_TARGET)
	-@cd $(MAIN_TARGET); \
        for html in *.html; \
            do $(TIDYCMD) $$html; \
        done

pub-dist: dist
	@echo "Publishing dist pages (*.html only)."
	scp dist/*.html $(DIST_PUB_DEST)

install: main dist
	@cp -R dist/. ..
	@mkdir -p ../../main-`cat DISTNAME`/.
	@cp -R main/. ../../main-`cat DISTNAME`/.

weblint:
	-weblint -x netscape -d extension-attribute -e img-size $(MAIN_TARGET)
	-weblint -x netscape -d extension-attribute -e img-size $(DIST_TARGET)

clean: 
	@rm -rf $(MAIN_TARGET)
	@rm -rf $(DIST_TARGET)
	@rm -rf $(DOC_CONTENTS_MAIN)
	@rm -rf $(DOC_CONTENTS_DIST)
	@find . -name "*~" -type f -print | xargs rm -f
