#!/bin/csh
# Executed from the main Isabelle directory, this script removes all files
# made when Isabelle was used with set MAKE_HTML

rm */.theory_list.txt */*/.theory_list.txt */*/*/.theory_list.txt \
   */index.html */*/index.html */*/*/index.html \
   */.*.html */*/.*.html */*/*/.*.html
