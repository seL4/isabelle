(*  Title:      HOL/ex/NatSum.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Summing natural numbers, squares and cubes.  Could be continued...

Originally demonstrated permutative rewriting, but add_ac is no longer needed
  thanks to new simprocs.
*)

(*The sum of the first n odd numbers equals n squared.*)
Goal "sum (%i. Suc(i+i)) n = n*n";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_odds";

(*The sum of the first n positive integers equals n(n+1)/2.*)
Goal "2 * sum id (Suc n) = n*Suc(n)";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_naturals";

Addsimps [add_mult_distrib, add_mult_distrib2];

Goal "Suc(Suc(Suc(Suc 2))) * sum (%i. i*i) (Suc n) = n * Suc(n) * Suc(2*n)";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_squares";

Goal "Suc(Suc 2) * sum (%i. i*i*i) (Suc n) = n * n * Suc(n) * Suc(n)";
by (induct_tac "n" 1);
by Auto_tac;
qed "sum_of_cubes";
