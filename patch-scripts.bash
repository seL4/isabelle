#
# $Id$
#
# patch-scripts.bash - relocate interpreter paths of Isabelle scripts.
#

## find binaries

function findbin()
{
  local DEFAULT="$1"
  local BASE=""
  local BINARY=""

  if [ -f "$DEFAULT" ]; then	# preferred location
    echo "found $DEFAULT" >&2
    echo "$DEFAULT"
    return
  else				# find in PATH
    BASE=$(basename "$DEFAULT")
    BINARY=$(type -path "$BASE")
    if [ -n "$BINARY" ]; then
      echo "found $BINARY" >&2
      echo "$BINARY"
      return
    else
      echo "WARNING: $BASE not found!" >&2
      echo "$DEFAULT"
      return
    fi
  fi
}


## main

BASH=$(findbin /bin/bash)
PERL=$(findbin /usr/bin/perl)

for FILE in $(find . -type f -print)
do
  if [ -x "$FILE" ]; then
    sed -e "s:^#!.*/bash:#!$BASH:" -e "s:^#!.*/perl:#!$PERL:" $FILE >$FILE~~
    if cmp $FILE $FILE~~ -s; then
      rm $FILE~~
    else
      rm -f $FILE
      mv $FILE~~ $FILE
      chmod +x $FILE
      echo fixed $FILE
    fi
  fi
done
