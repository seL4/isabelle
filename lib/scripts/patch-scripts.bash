#
# $Id$
# Author: Markus Wenzel, TU Muenchen
# License: GPL (GNU GENERAL PUBLIC LICENSE)
#
# patch-scripts.bash - relocate interpreter paths of executable scripts and
#   insert AUTO_BASH/AUTO_PERL values
#

## find binaries

function findbin()
{
  local BASE="$1"
  local BINARY=""

  BINARY=$(type -path "$BASE")

  if [ -n "$BINARY" ]; then
    echo "found $BINARY" >&2
    echo "$BINARY"
    return
  else
    echo "ERROR: $BASE not found!" >&2
    echo "$DEFAULT"
    return
  fi
}


## main

[ -z "$BASH_PATH" ] && BASH_PATH=$(findbin bash)
[ -z "$PERL_PATH" ] && PERL_PATH=$(findbin perl)
[ -z "$AUTO_BASH" ] && AUTO_BASH="$BASH_PATH"
[ -z "$AUTO_PERL" ] && AUTO_PERL="$PERL_PATH"

for FILE in $(find . -type f -print)
do
  if [ -x "$FILE" ]; then
    sed -e "s:^#!.*/bash:#!$BASH_PATH:" -e "s:^#!.*/perl:#!$PERL_PATH:" \
      -e "s:^AUTO_BASH=.*bash:AUTO_BASH=$AUTO_BASH:" \
      -e "s:^AUTO_PERL=.*perl:AUTO_PERL=$AUTO_PERL:" "$FILE" > "$FILE~~"
    if cmp -s "$FILE" "$FILE~~"; then
      rm "$FILE~~"
    else
      rm -f "$FILE"
      mv "$FILE~~" "$FILE"
      chmod +x "$FILE"
      echo "fixed $FILE"
    fi
  fi
done
