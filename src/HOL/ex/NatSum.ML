(*  Title:      HOL/ex/NatSum.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Summing natural numbers, squares and cubes.  Could be continued...
Demonstrates permutative rewriting.
*)

Addsimps add_ac;
Addsimps [add_mult_distrib, add_mult_distrib2];

(*The sum of the first n positive integers equals n(n+1)/2.*)
goal NatSum.thy "2*sum (%i.i) (Suc n) = n*Suc(n)";
by (Simp_tac 1);
by (nat_ind_tac "n" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "sum_of_naturals";

goal NatSum.thy
  "Suc(Suc(Suc(Suc(Suc(Suc(0))))))*sum (%i.i*i) (Suc n) = n*Suc(n)*Suc(2*n)";
by (Simp_tac 1);
by (nat_ind_tac "n" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "sum_of_squares";

goal NatSum.thy
  "Suc(Suc(Suc(Suc(0))))*sum (%i.i*i*i) (Suc n) = n*n*Suc(n)*Suc(n)";
by (Simp_tac 1);
by (nat_ind_tac "n" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "sum_of_cubes";

(*The sum of the first n odd numbers equals n squared.*)
goal NatSum.thy "sum (%i.Suc(i+i)) n = n*n";
by (nat_ind_tac "n" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "sum_of_odds";

