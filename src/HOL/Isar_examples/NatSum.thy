(*  Title:      HOL/Isar_examples/NatSum.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel
*)

theory NatSum = Main:;

section {* Summing natural numbers *};

text {* A summation operator: sum f (n+1) is the sum of all f(i), i=0...n. *};

consts
  sum	:: "[nat => nat, nat] => nat";

primrec 
  "sum f 0 = 0"
  "sum f (Suc n) = f n + sum f n";


(*theorems [simp] = add_assoc add_commute add_left_commute add_mult_distrib add_mult_distrib2;*)


subsection {* The sum of the first n positive integers equals n(n+1)/2 *};

text {* Emulate Isabelle proof script: *};

(*
  Goal "2*sum (%i. i) (Suc n) = n*Suc(n)";
  by (Simp_tac 1);
  by (induct_tac "n" 1);
  by (Simp_tac 1);
  by (Asm_simp_tac 1);
  qed "sum_of_naturals";
*)

theorem sum_of_naturals: "2 * sum (%i. i) (Suc n) = n * Suc n";
proof -;
  apply simp_tac;
  apply (induct n);
  apply simp_tac;
  apply asm_simp_tac;
qed;


text {* Proper Isabelle/Isar proof expressing the same reasoning (which
  is apparently not the most natural one): *};

theorem sum_of_naturals: "2 * sum (%i. i) (Suc n) = n * Suc n";
proof simp;
  show "n + (sum (%i. i) n + sum (%i. i) n) = n * n" (is "??P n");
  proof (induct ??P n);
    show "??P 0"; by simp;
    fix m; assume hyp: "??P m"; show "??P (Suc m)"; by (simp, rule hyp);
  qed;
qed;


subsection {* The sum of the first n odd numbers equals n squared *};

text {* First version: `proof-by-induction' *};

theorem sum_of_odds: "sum (%i. Suc (i + i)) n = n * n" (is "??P n");
proof (induct n);
  show "??P 0"; by simp;
  fix m; assume hyp: "??P m"; show "??P (Suc m)"; by (simp, rule hyp);
qed;

text {* The second version tells more about what is going on during the
induction. *};

theorem sum_of_odds': "sum (%i. Suc (i + i)) n = n * n" (is "??P n");
proof (induct n);
  show "??P 0" (is "sum (%i. Suc (i + i)) 0 = 0 * 0"); by simp;
  fix m; assume hyp: "??P m";
  show "??P (Suc m)" (is "sum (%i. Suc (i + i)) (Suc m) = Suc m * Suc m");
    by (simp, rule hyp);
qed;


end;
