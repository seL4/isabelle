(*  Title: 	HOL/ex/natsum.ML
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1994 TU Muenchen

Summing natural numbers, squares and cubes. Could be continued...
*)

val natsum_ss = arith_ss addsimps
  ([NatSum.sum_0,NatSum.sum_Suc] @ add_ac);

(*The sum of the first n positive integers equals n(n+1)/2.*)
goal NatSum.thy "Suc(Suc(0))*sum (%i.i) (Suc n) = n*Suc(n)";
by (simp_tac natsum_ss 1);
by (nat_ind_tac "n" 1);
by (simp_tac natsum_ss 1);
by (asm_simp_tac natsum_ss 1);
qed "sum_of_naturals";

goal NatSum.thy
  "Suc(Suc(Suc(Suc(Suc(Suc(0))))))*sum (%i.i*i) (Suc n) = \
\  n*Suc(n)*Suc(Suc(Suc(0))*n)";
by (simp_tac natsum_ss 1);
by (nat_ind_tac "n" 1);
by (simp_tac natsum_ss 1);
by (asm_simp_tac natsum_ss 1);
qed "sum_of_squares";

goal NatSum.thy
  "Suc(Suc(Suc(Suc(0))))*sum (%i.i*i*i) (Suc n) = n*n*Suc(n)*Suc(n)";
by (simp_tac natsum_ss 1);
by (nat_ind_tac "n" 1);
by (simp_tac natsum_ss 1);
by (asm_simp_tac natsum_ss 1);
qed "sum_of_cubes";

(*The sum of the first n odd numbers equals n squared.*)
goal NatSum.thy "sum (%i.Suc(i+i)) n = n*n";
by (nat_ind_tac "n" 1);
by (simp_tac natsum_ss 1);
by (asm_simp_tac natsum_ss 1);
qed "sum_of_odds";

