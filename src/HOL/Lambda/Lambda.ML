(*  Title:      HOL/Lambda/Lambda.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Substitution-lemmas.
*)

(*** Lambda ***)

open Lambda;

Delsimps [subst_Var];
Addsimps ([if_not_P, not_less_eq] @ beta.intrs);

(* don't add r_into_rtrancl! *)
AddSIs beta.intrs;

val dB_case_distinction =
  rule_by_tactic(EVERY[etac thin_rl 2,etac thin_rl 2,etac thin_rl 3])dB.induct;

(*** Congruence rules for ->> ***)

Goal "s ->> s' ==> Abs s ->> Abs s'";
by (etac rtrancl_induct 1);
by (ALLGOALS (blast_tac (claset() addIs [rtrancl_into_rtrancl])));
qed "rtrancl_beta_Abs";
AddSIs [rtrancl_beta_Abs];

Goal "s ->> s' ==> s $ t ->> s' $ t";
by (etac rtrancl_induct 1);
by (ALLGOALS (blast_tac (claset() addIs [rtrancl_into_rtrancl])));
qed "rtrancl_beta_AppL";

Goal "t ->> t' ==> s $ t ->> s $ t'";
by (etac rtrancl_induct 1);
by (ALLGOALS (blast_tac (claset() addIs [rtrancl_into_rtrancl])));
qed "rtrancl_beta_AppR";

Goal "[| s ->> s'; t ->> t' |] ==> s $ t ->> s' $ t'";
by (blast_tac (claset() addSIs [rtrancl_beta_AppL, rtrancl_beta_AppR]
                       addIs  [rtrancl_trans]) 1);
qed "rtrancl_beta_App";
AddIs [rtrancl_beta_App];

(*** subst and lift ***)

fun addsplit ss = ss addsimps [subst_Var]
                     delsplits [split_if]
                     setloop (split_inside_tac [split_if]);

Goal "(Var k)[u/k] = u";
by (asm_full_simp_tac(addsplit(simpset())) 1);
qed "subst_eq";

Goal "i<j ==> (Var j)[u/i] = Var(j-1)";
by (asm_full_simp_tac(addsplit(simpset())) 1);
qed "subst_gt";

Goal "j<i ==> (Var j)[u/i] = Var(j)";
by (asm_full_simp_tac (addsplit(simpset()) addsimps
                          [less_not_refl2 RS not_sym,less_SucI]) 1);
qed "subst_lt";

Addsimps [subst_eq,subst_gt,subst_lt];

Goal
  "!i k. i < Suc k --> lift (lift t i) (Suc k) = lift (lift t k) i";
by (dB.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac (simpset() addSolver cut_trans_tac)));
by (safe_tac HOL_cs);
by (ALLGOALS trans_tac);
qed_spec_mp "lift_lift";

Goal "!i j s. j < Suc i --> lift (t[s/j]) i = (lift t (Suc i)) [lift s i / j]";
by (dB.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [diff_Suc,subst_Var,lift_lift]
                                addsplits [split_nat_case]
                                addSolver cut_trans_tac)));
by (safe_tac HOL_cs);
by (ALLGOALS trans_tac);
qed "lift_subst";
Addsimps [lift_subst];

Goal
  "!i j s. i < Suc j --> lift (t[s/j]) i = (lift t i) [lift s i / Suc j]";
by (dB.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [subst_Var,lift_lift]
                                addSolver cut_trans_tac)));
by (safe_tac (HOL_cs addSEs [nat_neqE]));
by (ALLGOALS trans_tac);
qed "lift_subst_lt";

Goal "!k s. (lift t k)[s/k] = t";
by (dB.induct_tac "t" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "subst_lift";
Addsimps [subst_lift];


Goal "!i j u v. i < Suc j --> t[lift v i / Suc j][u[v/j]/i] = t[u/i][v/j]";
by (dB.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac
      (simpset() addsimps [diff_Suc,subst_Var,lift_lift RS sym,lift_subst_lt]
                 delsplits [split_if]
                 addsplits [split_nat_case]
                 addloop ("if",split_inside_tac[split_if])
                addSolver cut_trans_tac)));
by (safe_tac (HOL_cs addSEs [nat_neqE]));
by (ALLGOALS trans_tac);
qed_spec_mp "subst_subst";


(*** Equivalence proof for optimized substitution ***)

Goal "!k. liftn 0 t k = t";
by (dB.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac(addsplit(simpset()))));
qed "liftn_0";
Addsimps [liftn_0];

Goal "!k. liftn (Suc n) t k = lift (liftn n t k) k";
by (dB.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac(addsplit(simpset()))));
by (blast_tac (claset() addDs [add_lessD1]) 1);
qed "liftn_lift";
Addsimps [liftn_lift];

Goal "!n. substn t s n = t[liftn n s 0 / n]";
by (dB.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac(addsplit(simpset()))));
qed "substn_subst_n";
Addsimps [substn_subst_n];

Goal "substn t s 0 = t[s/0]";
by (Simp_tac 1);
qed "substn_subst_0";
