# -*- shell-script -*- :mode=shellscript:
#
# Author: Makarius
#
# timestart - setup bash environment for timing.
#

TIMES_RESULT=""

function get_times () {
  local TMP="/tmp/get_times$$"
  times > "$TMP"   # No pipe here!
  TIMES_RESULT="$SECONDS $(echo $(cat "$TMP") | perl -pe 's,\d+m\d+\.\d+s \d+m\d+\.\d+s (\d+)m(\d+)\.\d+s +(\d+)m(\d+)\.\d+s, $1 * 60 + $2 + $3 * 60 + $4,e')"
  rm -f "$TMP"
}

get_times  # sets TIMES_RESULT
