#!/usr/bin/env bash
# $Id$

# build make dependency file

# parameters
FIND="$1"
OUTPUTROOT="$2"
DEP_FILE="$3"
STATICDIRS="$4"
STATICFILES="$5"

rm -f "$DEP_FILE"
touch "$DEP_FILE"
echo '# This is a generated file; do not edit' >> "$DEP_FILE"
echo >> "$DEP_FILE"
allstatic=''
for dir in $STATICDIRS
do
    for file in $("$FIND" "$dir" -follow -type f -a ! -path "*/CVS/*" -a ! -path "*/.svn/*")
    do
        outputfile="\$(OUTPUTROOT)/$file"
        echo "$outputfile: $file" >> "$DEP_FILE"
        echo '	mkdir -p $(dir $@)' >> "$DEP_FILE"
        echo '	-chmod $(TARGET_UMASK_DIR) $(dir $@)' >> "$DEP_FILE"
        echo '	-chgrp $(TARGET_GROUP) $(dir $@)' >> "$DEP_FILE"
        echo '	-[ -e $@ ] && rm $@' >> "$DEP_FILE"
        echo '	cp $< $@' >> "$DEP_FILE"
        echo '	chmod $(TARGET_UMASK_FILE) $@' >> "$DEP_FILE"
        echo '	chgrp $(TARGET_GROUP) $@' >> "$DEP_FILE"
        allstatic="$allstatic$outputfile "
        echo >> "$DEP_FILE"
    done
done
echo "DEP_ALLSTATIC=$allstatic" >> "$DEP_FILE"
echo >> "$DEP_FILE"
echo 'DEP_HTML=$(DEP_ALLSTATIC) $(STATICFILES) $(DEP_FILE) $(CONF)' >> "$DEP_FILE"
echo >> "$DEP_FILE"
allhtml=''
for html in $("$FIND" . -name "*.html" -a ! -name "*.include.html")
do
    outputfile="\$(OUTPUTROOT)/$html"
    echo "$outputfile: $html \$(DEP_HTML)" >> "$DEP_FILE"
    echo '	mkdir -p $(dir $@)' >> "$DEP_FILE"
    echo '	-chmod $(TARGET_UMASK_DIR) $(dir $@)' >> "$DEP_FILE"
    echo '	-chgrp $(TARGET_GROUP) $(dir $@)' >> "$DEP_FILE"
    echo '	-[ -e $@ ] && rm $@' >> "$DEP_FILE"
    echo '	$(PYTHON) build/pypager.py --dtd="dtd/" $(FORCE_ENC_CMD) --srcroot="." --dstroot="$(OUTPUTROOT)" distname="$(DISTNAME)" $< $@' >> "$DEP_FILE"
    echo '	-$(TIDYCMD) $@' >> "$DEP_FILE"
    echo '	chmod $(TARGET_UMASK_FILE) $@' >> "$DEP_FILE"
    echo '	chgrp $(TARGET_GROUP) $@' >> "$DEP_FILE"
    allhtml="$allhtml$outputfile "
    echo >> "$DEP_FILE"
done
echo "DEP_ALLHTML=$allhtml" >> "$DEP_FILE"
echo >> "$DEP_FILE"
echo 'allsite: $(DEP_ALLHTML) $(DEP_ALLSTATIC)' >> "$DEP_FILE"
echo '	$(PYTHON) build/obfusmail.py --dtd="dtd/" --dstroot="$(OUTPUTROOT)" --dstdir="img"' "$allhtml" >> "$DEP_FILE"
echo ".PHONY: allsite" >> "$DEP_FILE"
