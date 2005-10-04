#!/usr/bin/env bash
# $Id$

# set permissions for local files

# parameters
FIND="$1"
LOCAL_UMASK_FILE="$2"
LOCAL_UMASK_DIR="$3"
LOCAL_GROUP="$4"

for file in $("$FIND" .)
do
    if [ -O "$file" ]
    then
        echo "$file..."
        if [ -d "$file" ]
        then
            chmod "$LOCAL_UMASK_DIR" "$file"
        else
            if [ -x "$file" ]
            then
                chmod "$LOCAL_UMASK_FILE",u+x,g+x,o+x "$file"
            else
                chmod "$LOCAL_UMASK_FILE" "$file"
            fi
        fi
    fi
done
