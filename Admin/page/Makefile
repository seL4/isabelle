# --- uses $DISTNAME environment variable 

# --- perl scripts used in this makefile

GENPAGE   = bin/genpage
MKCONTENT = bin/mkcontents

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
DOC_CONTENT_FILE = ../../Distribution/doc/Contents

# --- url prefixes for documentation links in main and dist dirs
DIST_DOCU_PREFIX = $(DISTNAME)/doc/
MAIN_DOCU_PREFIX = dist/$(DISTNAME)/doc/

# --- target include files with documentation links
DOC_CONTENTS_MAIN = docu-contents.main
DOC_CONTENTS_DIST = docu-contents.dist

# ---
# --- begin rules

all: clean gen

gen: main dist

main: check
	$(MKCONTENT) -p $(MAIN_DOCU_PREFIX) $(DOC_CONTENT_FILE) $(DOC_CONTENTS_MAIN)
	$(GENPAGE) -t $(MAIN_LAYOUT)/$(TEMPLATE_NAME) -c $(MAIN_CONTENT) -o $(MAIN_TARGET)

	cd $(MAIN_TARGET); perl -pi -e "s/{ISABELLE}/$(DISTNAME)/g;" *.html

dist: check
	$(MKCONTENT) -p $(DIST_DOCU_PREFIX) $(DOC_CONTENT_FILE) $(DOC_CONTENTS_DIST)
	$(GENPAGE) -t $(DIST_LAYOUT)/$(TEMPLATE_NAME) -c $(DIST_CONTENT) -o $(DIST_TARGET)

	cd $(DIST_TARGET); perl -pi -e "s/{ISABELLE}/$(DISTNAME)/g;" *.html

clean: 
	rm -rf $(MAIN_TARGET)
	rm -rf $(DIST_TARGET)
	rm -rf $(DOC_CONTENTS_MAIN)
	rm -rf $(DOC_CONTENTS_DIST)
	rm -f `find . -name "*~" -type f`

check:
	@if [ "$(DISTNAME)" = "" ]; then echo "Error: \$$DISTNAME not set."; exit 1; fi
