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

val db_case_distinction =
  rule_by_tactic(EVERY[etac thin_rl 2,etac thin_rl 2,etac thin_rl 3])db.induct;

(*** Congruence rules for ->> ***)

goal Lambda.thy "!!s. s ->> s' ==> Fun s ->> Fun s'";
by (etac rtrancl_induct 1);
by (ALLGOALS(fast_tac (!claset addIs [rtrancl_into_rtrancl])));
qed "rtrancl_beta_Fun";
AddSIs [rtrancl_beta_Fun];

goal Lambda.thy "!!s. s ->> s' ==> s @ t ->> s' @ t";
by (etac rtrancl_induct 1);
by (ALLGOALS(fast_tac (!claset addIs [rtrancl_into_rtrancl])));
qed "rtrancl_beta_AppL";

goal Lambda.thy "!!s. t ->> t' ==> s @ t ->> s @ t'";
by (etac rtrancl_induct 1);
by (ALLGOALS(fast_tac (!claset addIs [rtrancl_into_rtrancl])));
qed "rtrancl_beta_AppR";

goal Lambda.thy "!!s. [| s ->> s'; t ->> t' |] ==> s @ t ->> s' @ t'";
by (deepen_tac (!claset addSIs [rtrancl_beta_AppL,rtrancl_beta_AppR]
                        addIs  [rtrancl_trans]) 3 1);
qed "rtrancl_beta_App";
AddIs [rtrancl_beta_App];

(*** subst and lift ***)

fun addsplit ss = ss addsimps [subst_Var] setloop (split_inside_tac [expand_if]);

goal Lambda.thy "(Var k)[u/k] = u";
by (asm_full_simp_tac(addsplit(!simpset)) 1);
qed "subst_eq";

goal Lambda.thy "!!s. i<j ==> (Var j)[u/i] = Var(pred j)";
by (asm_full_simp_tac(addsplit(!simpset)) 1);
qed "subst_gt";

goal Lambda.thy "!!s. j<i ==> (Var j)[u/i] = Var(j)";
by (asm_full_simp_tac (addsplit(!simpset) addsimps
                          [less_not_refl2 RS not_sym,less_SucI]) 1);
qed "subst_lt";

Addsimps [subst_eq,subst_gt,subst_lt];

goal Lambda.thy
  "!i k. i < Suc k --> lift (lift t i) (Suc k) = lift (lift t k) i";
by (db.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac (!simpset setloop (split_tac [expand_if])
                                    addsolver (cut_trans_tac))));
by (safe_tac HOL_cs);
by (ALLGOALS trans_tac);
qed_spec_mp "lift_lift";

goal Lambda.thy "!i j s. j < Suc i --> \
\         lift (t[s/j]) i = (lift t (Suc i)) [lift s i / j]";
by (db.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac (!simpset addsimps [pred_def,subst_Var,lift_lift]
                                setloop (split_tac [expand_if,expand_nat_case])
                                addsolver (cut_trans_tac))));
by (safe_tac HOL_cs);
by (ALLGOALS trans_tac);
qed "lift_subst";
Addsimps [lift_subst];

goal Lambda.thy
  "!i j s. i < Suc j -->\
\         lift (t[s/j]) i = (lift t i) [lift s i / Suc j]";
by (db.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac (!simpset addsimps [subst_Var,lift_lift]
                                setloop (split_tac [expand_if])
                                addsolver (cut_trans_tac))));
by(safe_tac (HOL_cs addSEs [nat_neqE]));
by(ALLGOALS trans_tac);
qed "lift_subst_lt";

goal Lambda.thy "!k s. (lift t k)[s/k] = t";
by (db.induct_tac "t" 1);
by (ALLGOALS (asm_full_simp_tac (!simpset setloop (split_tac[expand_if]))));
qed "subst_lift";
Addsimps [subst_lift];


goal Lambda.thy "!i j u v. i < Suc j --> \
\ t[lift v i / Suc j][u[v/j]/i] = t[u/i][v/j]";
by (db.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac
      (!simpset addsimps [pred_def,subst_Var,lift_lift RS sym,lift_subst_lt]
                setloop (split_tac [expand_if,expand_nat_case])
                addsolver (cut_trans_tac))));
by(safe_tac (HOL_cs addSEs [nat_neqE]));
by(ALLGOALS trans_tac);
qed_spec_mp "subst_subst";


(*** Equivalence proof for optimized substitution ***)

goal Lambda.thy "!k. liftn 0 t k = t";
by (db.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac(addsplit(!simpset))));
qed "liftn_0";
Addsimps [liftn_0];

goal Lambda.thy "!k. liftn (Suc n) t k = lift (liftn n t k) k";
by (db.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac(addsplit(!simpset))));
by (fast_tac (HOL_cs addDs [add_lessD1]) 1);
qed "liftn_lift";
Addsimps [liftn_lift];

goal Lambda.thy "!n. substn t s n = t[liftn n s 0 / n]";
by (db.induct_tac "t" 1);
by (ALLGOALS(asm_simp_tac(addsplit(!simpset))));
qed "substn_subst_n";
Addsimps [substn_subst_n];

goal Lambda.thy "substn t s 0 = t[s/0]";
by (Simp_tac 1);
qed "substn_subst_0";
