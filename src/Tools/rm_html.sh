#!/bin/csh
# Executed from the main Isabelle directory, this script removes all files
# made when Isabelle was used with set MAKE_HTML

rm */theory_list.txt */index.html */Pure_sub.html */CPure_sub.html
foreach f (*/*.thy */*/*.thy */*/*/*.thy)
  if (-f $f:r.html) then
    rm $f:r.html $f:r_sub.html $f:r_sup.html
  endif
end
