# -*- shell-script -*-
# $Id$
# Author: Makarius
#
# timestart - setup bash environment for timing.
#

TIMES_RESULT=""

#set by configure
AUTO_PERL=perl

function get_times () {
  local TMP="/tmp/get_times$$"
  times > "$TMP"   # No pipe here!
  TIMES_RESULT="$SECONDS $(tail -1 "$TMP" | "$AUTO_PERL" -pe 's,(\d+)m(\d+)\.\d+s, $1 * 60 + $2,ge')"
  /bin/rm -f "$TMP"
}

get_times  # sets TIMES_RESULT

