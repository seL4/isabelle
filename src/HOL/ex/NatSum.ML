(*  Title:      HOL/ex/NatSum.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Summing natural numbers, squares, cubes, etc.

Originally demonstrated permutative rewriting, but add_ac is no longer needed
  thanks to new simprocs.
*)

(*The sum of the first n odd numbers equals n squared.*)
Goal "sum (%i. Suc(i+i)) n = n*n";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_odds";

Addsimps [add_mult_distrib, add_mult_distrib2];

(*The sum of the first n positive integers equals n(n+1)/2.*)
Goal "#2 * sum id (Suc n) = n*Suc(n)";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_naturals";

Goal "#6 * sum (%i. i*i) (Suc n) = n * Suc(n) * Suc(#2*n)";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_squares";

Goal "#4 * sum (%i. i*i*i) (Suc n) = n * n * Suc(n) * Suc(n)";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_cubes";

(** Sum of fourth powers requires lemmas **)

Goal "[| #1 <= (j::nat); k <= m |] ==> k <= j*m";
by (dtac mult_le_mono 1);
by Auto_tac;
qed "mult_le_1_mono";

Addsimps [diff_mult_distrib, diff_mult_distrib2];

(*Thanks to Sloane's On-Line Encyclopedia of Integer Sequences,
  http://www.research.att.com/~njas/sequences/*)
Goal "#30 * sum (%i. i*i*i*i) (Suc n) = \
\     n * Suc(n) * Suc(#2*n) * (#3*n*n + #3*n - #1)";
by (induct_tac "n" 1);
by (Simp_tac 1);
(*Automating this inequality proof would make the proof trivial*)
by (subgoal_tac "n <= #10 * (n * (n * n)) + (#15 * (n * (n * (n * n))) + \
\                     #6 * (n * (n * (n * (n * n)))))" 1);
(*In simplifying we want only the outer Suc argument to be unfolded.
  Thus the result matches the induction hypothesis (also with Suc). *)
by (asm_simp_tac (simpset() delsimps [sum_Suc]
                            addsimps [inst "n" "Suc ?m" sum_Suc]) 1);
by (rtac ([mult_le_1_mono, le_add1] MRS le_trans) 1);
by (rtac le_cube 2);
by (Simp_tac 1);
qed "sum_of_fourth_powers";

(** Alternative proof, avoiding the need for inequality reasoning **)

Addsimps [zmult_int RS sym, zadd_zmult_distrib, zadd_zmult_distrib2, 
	  zdiff_zmult_distrib, zdiff_zmult_distrib2];

Goal "#30 * int (sum (%i. i*i*i*i) (Suc n)) = \
\     int n * int(Suc n) * int (Suc(#2*n)) * (int (#3*n*n) + int (#3*n) - #1)";
by (induct_tac "n" 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() delsimps [sum_Suc]
                            addsimps [inst "n" "Suc ?m" sum_Suc]) 1);
qed "int_sum_of_fourth_powers";


