(*  Title:      ZF/UNITY/NatPlus.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

More theorems on naturals

*)

Goal "[| m:nat; n:nat |] \
\  ==> (m < succ(n)) <-> (m = 0 | (EX j:nat. m = succ(j) & j < n))";
by (induct_tac "m" 1);
by Auto_tac;
qed "lt_succ_eq_0_disj";

(***** HAVE BEEN MOVED TO ZF BY LCP 
Goal "[| m:nat; n:nat |] ==> m #- n = 0 <-> m le n";
by (auto_tac (claset(), simpset() addsimps [le_iff, diff_self_eq_0]));
by (force_tac (claset(), simpset() addsimps [less_iff_succ_add ]) 2);
by (res_inst_tac [("Pa", "False")] swap 1);
by (ALLGOALS(asm_full_simp_tac (simpset() 
                addsimps [not_lt_iff_le, le_iff])));
by (auto_tac (claset(), simpset() addsimps [zero_less_diff RS iff_sym]));
qed "diff_is_0_iff2";


Goal  "m #- n = 0 <-> natify(m) le natify(n)";
by (asm_simp_tac (simpset() addsimps [diff_is_0_iff2 RS iff_sym]) 1);
qed "diff_is_0_iff";

Goal "n:nat ==> natify(n)=0 <-> n=0";
by (Asm_simp_tac 1);
qed "natify_of_nat_is_0_iff";
Addsimps [natify_of_nat_is_0_iff];

Goal "n:nat ==> 0 = natify(n) <-> n=0";
by Auto_tac;
qed "natify_of_nat_is_0_iff2";
Addsimps [natify_of_nat_is_0_iff2];

Goal "[| a:nat; b:nat |] ==> \
\ (P(a #- b)) <-> ((a < b -->P(0)) & (ALL d:nat. a = b #+ d --> P(d)))";
by (case_tac "a le b" 1);
by (asm_full_simp_tac (simpset() 
           addsimps [diff_is_0_iff2 RS iff_sym]) 1);
by Safe_tac;
by (ALLGOALS(asm_full_simp_tac (simpset() 
                 addsimps [le_iff, not_lt_iff_le])));
by Safe_tac;
by (ALLGOALS(rotate_tac ~1));
by (ALLGOALS(Asm_full_simp_tac));
by (dtac lt_not_sym 2);
by (Asm_full_simp_tac 2);
by (ALLGOALS(dres_inst_tac [("x", "a #- b")] bspec));
by (ALLGOALS(Asm_simp_tac));
by (ALLGOALS(dtac (leI RS add_diff_inverse)));
by (ALLGOALS(rotate_tac ~1));
by (ALLGOALS(Asm_full_simp_tac));
qed "nat_diff_split";
****)



