(*  Title:      HOL/ex/NatSum.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Lawrence C Paulson

Summing natural numbers, squares, cubes, etc.

Originally demonstrated permutative rewriting, but add_ac is no longer needed
  thanks to new simprocs.

Thanks to Sloane's On-Line Encyclopedia of Integer Sequences,
  http://www.research.att.com/~njas/sequences/
*)

Addsimps [zadd_zmult_distrib, zadd_zmult_distrib2];
Addsimps [zdiff_zmult_distrib, zdiff_zmult_distrib2];

(*The sum of the first n odd numbers equals n squared.*)
Goal "n \\<in> nat ==> sum (%i. i $+ i $+ #1, n) = $#n $* $#n";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_odds";

(*The sum of the first n odd squares*)
Goal "n \\<in> nat ==> #3 $* sum (%i. (i $+ i $+ #1) $* (i $+ i $+ #1), n) = \
\     $#n $* (#4 $* $#n $* $#n $- #1)";
by (induct_tac "n" 1);
by Auto_tac;  
qed "sum_of_odd_squares";

(*The sum of the first n odd cubes*)
Goal "n \\<in> nat \
\     ==> sum (%i. (i $+ i $+ #1) $* (i $+ i $+ #1) $* (i $+ i $+ #1), n) = \
\         $#n $* $#n $* (#2 $* $#n $* $#n $- #1)";
by (induct_tac "n" 1);
by Auto_tac;  
qed "sum_of_odd_cubes";

(*The sum of the first n positive integers equals n(n+1)/2.*)
Goal "n \\<in> nat ==> #2 $* sum(%i. i, succ(n)) = $#n $* $#succ(n)";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_naturals";

Goal "n \\<in> nat ==> #6 $* sum (%i. i$*i, succ(n)) = \
\                $#n $* ($#n $+ #1) $* (#2 $* $#n $+ #1)";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_squares";

Goal "n \\<in> nat ==> #4 $* sum (%i. i$*i$*i, succ(n)) = \
\                $#n $* $#n $* ($#n $+ #1) $* ($#n $+ #1)";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_cubes";

(** Sum of fourth powers **)

Goal "n \\<in> nat ==> \
\     #30 $* sum (%i. i$*i$*i$*i, succ(n)) = \
\     $#n $* ($#n $+ #1) $* (#2 $* $#n $+ #1) $* \
\     (#3 $* $#n $* $#n $+ #3 $* $#n $- #1)";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_fourth_powers";
