# -*- shell-script -*-
# $Id$
# Author: Makarius
#
# timestop - report timing based on environment (cf. timestart.bash)
#

TIMES_REPORT=""

function show_times ()
{
  local TIMES_START="$TIMES_RESULT"
  get_times
  local TIMES_STOP="$TIMES_RESULT"
  local KIND
  for KIND in 1 2 3
  do
    local START=$(echo "$TIMES_START" | cut -d " " -f $KIND)
    local STOP=$(echo "$TIMES_STOP" | cut -d " " -f $KIND)

    local TIME=$[ $STOP - $START ]
    local SECS=$[ $TIME % 60 ]
    [ $SECS -lt 10 ] && SECS="0$SECS"
    local MINUTES=$[ ($TIME / 60) % 60 ]
    [ $MINUTES -lt 10 ] && MINUTES="0$MINUTES"
    local HOURS=$[ $TIME / 3600 ]

    local KIND_NAME
    [ "$KIND" = 1 ] && KIND_NAME="elapsed time"
    [ "$KIND" = 2 ] && KIND_NAME="user"
    [ "$KIND" = 3 ] && KIND_NAME="system"
    local RESULT="${HOURS}:${MINUTES}:${SECS} ${KIND_NAME}"

    if [ -z "$TIMES_REPORT" ]; then
      TIMES_REPORT="$RESULT"
    else
      TIMES_REPORT="$TIMES_REPORT, $RESULT"
    fi
  done
}

show_times  # sets TIMES_REPORT

unset TIMES_RESULT get_times show_times
