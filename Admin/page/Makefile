# -- makefile for Isabelle web pages (dist and main)
# -- $Id$

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

# ---
# --- begin rules

all: clean main dist
	@echo "###"
	@echo "### Finished.  See main/ and dist/ for the resulting pages."
	@echo "###"

main:
	@$(MKCONTENT) -p dist/`cat DISTNAME`/doc/ $(DOC_CONTENT_FILE) $(DOC_CONTENTS_MAIN)
	@env DISTNAME=`cat DISTNAME` \
	  $(GENPAGE) -t $(MAIN_LAYOUT)/$(TEMPLATE_NAME) -c $(MAIN_CONTENT) -o $(MAIN_TARGET)

dist:
	@$(MKCONTENT) -p `cat DISTNAME`/doc/ $(DOC_CONTENT_FILE) $(DOC_CONTENTS_DIST)
	@env DISTNAME=`cat DISTNAME` \
	  $(GENPAGE) -t $(DIST_LAYOUT)/$(TEMPLATE_NAME) -c $(DIST_CONTENT) -o $(DIST_TARGET)

clean: 
	@rm -rf $(MAIN_TARGET)
	@rm -rf $(DIST_TARGET)
	@rm -rf $(DOC_CONTENTS_MAIN)
	@rm -rf $(DOC_CONTENTS_DIST)
	@find . -name "*~" -type f -print | xargs rm -f
