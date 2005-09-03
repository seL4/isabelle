(*  Title:      FOL/ex/nat2.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge
*)

Addsimps [pred_0, pred_succ, plus_0, plus_succ,
          nat_distinct1, nat_distinct2, succ_inject,
          leq_0, leq_succ_succ, leq_succ_0,
          lt_0_succ, lt_succ_succ, lt_0];


val prems = goal (the_context ())
    "[| P(0);  !!x. P(succ(x)) |] ==> All(P)";
by (rtac nat_ind 1);
by (REPEAT (resolve_tac (prems@[allI,impI]) 1));
qed "nat_exh";

Goal "~ n=succ(n)";
by (IND_TAC nat_ind Simp_tac "n" 1);
result();

Goal "~ succ(n)=n";
by (IND_TAC nat_ind Simp_tac "n" 1);
result();

Goal "~ succ(succ(n))=n";
by (IND_TAC nat_ind Simp_tac "n" 1);
result();

Goal "~ n=succ(succ(n))";
by (IND_TAC nat_ind Simp_tac "n" 1);
result();

Goal "m+0 = m";
by (IND_TAC nat_ind Simp_tac "m" 1);
qed "plus_0_right";

Goal "m+succ(n) = succ(m+n)";
by (IND_TAC nat_ind Simp_tac "m" 1);
qed "plus_succ_right";

Addsimps [plus_0_right, plus_succ_right];

Goal "~n=0 --> m+pred(n) = pred(m+n)";
by (IND_TAC nat_ind Simp_tac "n" 1);
result();

Goal "~n=0 --> succ(pred(n))=n";
by (IND_TAC nat_ind Simp_tac "n" 1);
result();

Goal "m+n=0 <-> m=0 & n=0";
by (IND_TAC nat_ind Simp_tac "m" 1);
result();

Goal "m <= n --> m <= succ(n)";
by (IND_TAC nat_ind Simp_tac "m" 1);
by (rtac (impI RS allI) 1);
by (ALL_IND_TAC nat_ind Simp_tac 1);
by (Fast_tac 1);
bind_thm("le_imp_le_succ", result() RS mp);

Goal "n<succ(n)";
by (IND_TAC nat_ind Simp_tac "n" 1);
result();

Goal "~ n<n";
by (IND_TAC nat_ind Simp_tac "n" 1);
result();

Goal "m < n --> m < succ(n)";
by (IND_TAC nat_ind Simp_tac "m" 1);
by (rtac (impI RS allI) 1);
by (ALL_IND_TAC nat_ind Simp_tac 1);
by (Fast_tac 1);
result();

Goal "m <= n --> m <= n+k";
by (IND_TAC nat_ind (simp_tac (simpset() addsimps [le_imp_le_succ]))
     "k" 1);
qed "le_plus";

Goal "succ(m) <= n --> m <= n";
by (res_inst_tac [("x","n")]spec 1);
by (ALL_IND_TAC nat_exh (simp_tac (simpset() addsimps [le_imp_le_succ])) 1);
qed "succ_le";

Goal "~m<n <-> n<=m";
by (IND_TAC nat_ind Simp_tac "n" 1);
by (rtac (impI RS allI) 1);
by (ALL_IND_TAC nat_ind Asm_simp_tac 1);
qed "not_less";

Goal "n<=m --> ~m<n";
by (simp_tac (simpset() addsimps [not_less]) 1);
qed "le_imp_not_less";

Goal "m<n --> ~n<=m";
by (cut_facts_tac [not_less] 1 THEN Fast_tac 1);
qed "not_le";

Goal "m+k<=n --> m<=n";
by (IND_TAC nat_ind (K all_tac) "k" 1);
by (Simp_tac 1);
by (rtac (impI RS allI) 1);
by (Simp_tac 1);
by (REPEAT (resolve_tac [allI,impI] 1));
by (cut_facts_tac [succ_le] 1);
by (Fast_tac 1);
qed "plus_le";

val prems = goal (the_context ()) "[| ~m=0;  m <= n |] ==> ~n=0";
by (cut_facts_tac prems 1);
by (REPEAT (etac rev_mp 1));
by (IND_TAC nat_exh Simp_tac "m" 1);
by (ALL_IND_TAC nat_exh Simp_tac 1);
qed "not0";

Goal "a<=a' & b<=b' --> a+b<=a'+b'";
by (IND_TAC nat_ind (simp_tac (simpset() addsimps [le_plus])) "b" 1);
by (resolve_tac [impI RS allI] 1);
by (resolve_tac [allI RS allI] 1);
by (ALL_IND_TAC nat_exh Asm_simp_tac 1);
qed "plus_le_plus";

Goal "i<=j --> j<=k --> i<=k";
by (IND_TAC nat_ind (K all_tac) "i" 1);
by (Simp_tac 1);
by (resolve_tac [impI RS allI] 1);
by (ALL_IND_TAC nat_exh Simp_tac 1);
by (rtac impI 1);
by (ALL_IND_TAC nat_exh Simp_tac 1);
by (Fast_tac 1);
qed "le_trans";

Goal "i < j --> j <=k --> i < k";
by (IND_TAC nat_ind (K all_tac) "j" 1);
by (Simp_tac 1);
by (resolve_tac [impI RS allI] 1);
by (ALL_IND_TAC nat_exh Simp_tac 1);
by (ALL_IND_TAC nat_exh Simp_tac 1);
by (ALL_IND_TAC nat_exh Simp_tac 1);
by (Fast_tac 1);
qed "less_le_trans";

Goal "succ(i) <= j <-> i < j";
by (IND_TAC nat_ind Simp_tac "j" 1);
by (resolve_tac [impI RS allI] 1);
by (ALL_IND_TAC nat_exh Asm_simp_tac 1);
qed "succ_le2";

Goal "i<succ(j) <-> i=j | i<j";
by (IND_TAC nat_ind Simp_tac "j" 1);
by (ALL_IND_TAC nat_exh Simp_tac 1);
by (resolve_tac [impI RS allI] 1);
by (ALL_IND_TAC nat_exh Simp_tac 1);
by (Asm_simp_tac 1);
qed "less_succ";
