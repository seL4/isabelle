(*  Title:      HOL/ex/NatSum.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Summing natural numbers, squares, cubes, etc.

Originally demonstrated permutative rewriting, but add_ac is no longer needed
  thanks to new simprocs.

Thanks to Sloane's On-Line Encyclopedia of Integer Sequences,
  http://www.research.att.com/~njas/sequences/
*)

Addsimps [lessThan_Suc, atMost_Suc];
Addsimps [add_mult_distrib, add_mult_distrib2];
Addsimps [diff_mult_distrib, diff_mult_distrib2];

(*The sum of the first n odd numbers equals n squared.*)
Goal "setsum (%i. Suc(i+i)) (lessThan n) = n*n";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_odds";

(*The sum of the first n odd squares*)
Goal "#3 * setsum (%i. Suc(i+i)*Suc(i+i)) (lessThan n) = n * (#4*n*n - #1)";
by (induct_tac "n" 1);
(*This removes the -#1 from the inductive step*)
by (case_tac "n" 2);
by Auto_tac;
qed "sum_of_odd_squares";

(*The sum of the first n odd cubes*)
Goal "setsum (%i. Suc(i+i)*Suc(i+i)*Suc(i+i)) (lessThan n) = n * n * (#2*n*n - #1)";
by (induct_tac "n" 1);
(*This removes the -#1 from the inductive step*)
by (case_tac "n" 2);
by Auto_tac;
qed "sum_of_odd_cubes";

(*The sum of the first n positive integers equals n(n+1)/2.*)
Goal "#2 * setsum id (atMost n) = n*Suc(n)";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_naturals";

Goal "#6 * setsum (%i. i*i) (atMost n) = n * Suc(n) * Suc(#2*n)";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_squares";

Goal "#4 * setsum (%i. i*i*i) (atMost n) = n * n * Suc(n) * Suc(n)";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_cubes";

(** Sum of fourth powers: two versions **)

Goal "#30 * setsum (%i. i*i*i*i) (atMost n) = \
\     n * Suc(n) * Suc(#2*n) * (#3*n*n + #3*n - #1)";
by (induct_tac "n" 1);
by Auto_tac;
(*Eliminates the subtraction*)
by (case_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "sum_of_fourth_powers";

(*Alternative proof, with a change of variables and much more subtraction, 
  performed using the integers.*)

Addsimps [zmult_int RS sym, zadd_zmult_distrib, zadd_zmult_distrib2, 
	  zdiff_zmult_distrib, zdiff_zmult_distrib2];

Goal "#30 * int (setsum (%i. i*i*i*i) (lessThan m)) = \
\         int m * (int m - #1) * (int (#2*m) - #1) * \
\         (int (#3*m*m) - int(#3*m) - #1)";
by (induct_tac "m" 1);
by (ALLGOALS Asm_simp_tac);
qed "int_sum_of_fourth_powers";

(** Sums of geometric series: 2, 3 and the general case **)

Goal "setsum (%i. #2^i) (lessThan n) = #2^n - 1";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_2_powers";

Goal "#2 * setsum (%i. #3^i) (lessThan n) = #3^n - 1";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_3_powers";

Goal "0<k ==> (k-1) * setsum (%i. k^i) (lessThan n) = k^n - 1";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_powers";
