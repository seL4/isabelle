#
# $Id$
#
# patch-scripts.bash - relocate interpreter paths of executable scripts.
#

## find binaries

function findbin()
{
  local DEFAULT="$1"
  local BASE=$(basename "$DEFAULT")
  local BINARY=""

  BINARY=$(type -path "$BASE")

  if [ -n "$BINARY" ]; then
    echo "using $BINARY" >&2
    echo "$BINARY"
    return
  elif [ -f "$DEFAULT" ]; then
    echo "using $DEFAULT" >&2
    echo "$DEFAULT"
    return
  else
    echo "WARNING: $BASE not found!" >&2
    echo "$DEFAULT"
    return
  fi
}


## main

BASH=$(findbin /bin/bash)
PERL=$(findbin /usr/bin/perl)

for FILE in $(find . -type f -print)
do
  if [ -x "$FILE" ]; then
    sed -e "s:^#!.*/bash:#!$BASH:" -e "s:^#!.*/perl:#!$PERL:" $FILE >$FILE~~
    if cmp -s $FILE $FILE~~; then
      rm $FILE~~
    else
      rm -f $FILE
      mv $FILE~~ $FILE
      chmod +x $FILE
      echo fixed $FILE
    fi
  fi
done
