(*  Title:      HOL/Lambda/Lambda.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Substitution-lemmas.  Most of the proofs, esp. those about natural numbers,
are ported from Ole Rasmussen's ZF development.  In ZF, m<=n is syntactic
sugar for m<Suc(n). In HOL <= is a separate operator. Hence we have to prove
some compatibility lemmas.
*)

(*** Nat ***)

goal Nat.thy "!!i. [| i < Suc j; j < k |] ==> i < k";
by (rtac le_less_trans 1);
by (assume_tac 2);
by(asm_full_simp_tac (!simpset addsimps [le_def]) 1);
by(fast_tac (HOL_cs addEs [less_asym,less_anti_refl]) 1);
qed "lt_trans1";

goal Nat.thy "!!i. [| i < j; j < Suc(k) |] ==> i < k";
by (etac less_le_trans 1);
by(asm_full_simp_tac (!simpset addsimps [le_def]) 1);
by(fast_tac (HOL_cs addEs [less_asym,less_anti_refl]) 1);
qed "lt_trans2";

val major::prems = goal Nat.thy
  "[| i < Suc j; i < j ==> P; i = j ==> P |] ==> P";
by (rtac (major RS lessE) 1);
by(ALLGOALS Asm_full_simp_tac);
by(resolve_tac prems 1 THEN etac sym 1);
by(fast_tac (HOL_cs addIs prems) 1);
qed "leqE";

goal Arith.thy "!!i. Suc i < j ==> i < pred j ";
by (rtac Suc_less_SucD 1);
by (Asm_simp_tac 1);
qed "lt_pred";

goal Arith.thy "!!i. [| i < Suc j; k < i |] ==> pred i < j ";
by (rtac Suc_less_SucD 1);
by (Asm_simp_tac 1);
qed "gt_pred";


(*** Lambda ***)

open Lambda;

Delsimps [less_Suc_eq, subst_Var];
Addsimps ([if_not_P, not_less_eq] @ beta.intrs);

(* don't add r_into_rtrancl! *)
val lambda_cs = trancl_cs addSIs beta.intrs;

(*** Congruence rules for ->> ***)

goal Lambda.thy "!!s. s ->> s' ==> Fun s ->> Fun s'";
by (etac rtrancl_induct 1);
by (ALLGOALS(fast_tac (lambda_cs addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_beta_Fun";

goal Lambda.thy "!!s. s ->> s' ==> s @ t ->> s' @ t";
by (etac rtrancl_induct 1);
by (ALLGOALS(fast_tac (lambda_cs addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_beta_AppL";

goal Lambda.thy "!!s. t ->> t' ==> s @ t ->> s @ t'";
by (etac rtrancl_induct 1);
by (ALLGOALS(fast_tac (lambda_cs addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_beta_AppR";

goal Lambda.thy "!!s. [| s ->> s'; t ->> t' |] ==> s @ t ->> s' @ t'";
by (fast_tac (lambda_cs addSIs [rtrancl_beta_AppL,rtrancl_beta_AppR]
                        addIs  [rtrancl_trans]) 1);
qed "rtrancl_beta_App";

(*** subst and lift ***)

fun addsplit ss = ss addsimps [subst_Var] setloop (split_tac [expand_if]);

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
by(db.induct_tac "t" 1);
by(ALLGOALS Asm_simp_tac);
by(strip_tac 1);
by (excluded_middle_tac "nat < i" 1);
by ((forward_tac [lt_trans2] 2) THEN (assume_tac 2));
by (ALLGOALS(asm_full_simp_tac (addsplit(!simpset) addsimps [less_SucI])));
bind_thm("lift_lift", result() RS spec RS spec RS mp);

goal Lambda.thy "!i j s. j < Suc i --> \
\         lift (t[s/j]) i = (lift t (Suc i)) [lift s i / j]";
by(db.induct_tac "t" 1);
by(ALLGOALS(asm_simp_tac (!simpset addsimps [lift_lift])));
by(strip_tac 1);
by (excluded_middle_tac "nat < j" 1);
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("j","nat")] leqE 1);
by (asm_full_simp_tac (addsplit(!simpset)
                       addsimps [less_SucI,gt_pred]) 1);
by (hyp_subst_tac 1);
by (Asm_simp_tac 1);
by (forw_inst_tac [("j","j")] lt_trans2 1);
by (assume_tac 1);
by (asm_full_simp_tac (addsplit(!simpset) addsimps [less_SucI]) 1);
qed "lift_subst";
Addsimps [lift_subst];

goal Lambda.thy
  "!i j s. i < Suc j -->\
\         lift (t[s/j]) i = (lift t i) [lift s i / Suc j]";
by(db.induct_tac "t" 1);
by(ALLGOALS(asm_simp_tac (!simpset addsimps [lift_lift])));
by(strip_tac 1);
by (excluded_middle_tac "nat < j" 1);
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("i","j")] leqE 1);
by (forward_tac  [lt_trans1] 1 THEN assume_tac 1);
by (ALLGOALS(asm_full_simp_tac
               (!simpset addsimps [less_SucI,gt_pred])));
by (hyp_subst_tac 1);
by (asm_full_simp_tac (!simpset addsimps [less_SucI]) 1);
by(split_tac [expand_if] 1);
by (asm_full_simp_tac (!simpset addsimps [less_SucI]) 1);
qed "lift_subst_lt";

goal Lambda.thy "!k s. (lift t k)[s/k] = t";
by(db.induct_tac "t" 1);
by(ALLGOALS Asm_simp_tac);
by(split_tac [expand_if] 1);
by(ALLGOALS Asm_full_simp_tac);
qed "subst_lift";
Addsimps [subst_lift];


goal Lambda.thy "!i j u v. i < Suc j --> \
\ t[lift v i / Suc j][u[v/j]/i] = t[u/i][v/j]";
by(db.induct_tac "t" 1);
by(ALLGOALS(asm_simp_tac(!simpset addsimps [lift_lift RS sym,lift_subst_lt])));
by(strip_tac 1);
by (excluded_middle_tac "nat < Suc(Suc j)" 1);
by(Asm_full_simp_tac 1);
by (forward_tac [lessI RS less_trans] 1);
by (etac leqE 1);
by (asm_simp_tac (!simpset addsimps [lt_pred]) 2);
by (forward_tac [Suc_mono RS less_trans] 1 THEN assume_tac 1);
by (forw_inst_tac [("i","i")] (lessI RS less_trans) 1);
by (asm_simp_tac (!simpset addsimps [lt_pred]) 1);
by (eres_inst_tac [("i","nat")] leqE 1);
by (asm_full_simp_tac (!simpset addsimps [less_SucI]) 2);
by (excluded_middle_tac "nat < i" 1);
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("j","nat")] leqE 1);
by (asm_simp_tac (!simpset addsimps [gt_pred]) 1);
by (Asm_simp_tac 1);
by (forward_tac [lt_trans2] 1 THEN assume_tac 1);
by (asm_simp_tac (!simpset addsimps [gt_pred]) 1);
bind_thm("subst_subst", result() RS spec RS spec RS spec RS spec RS mp);


(*** Equivalence proof for optimized substitution ***)

goal Lambda.thy "!k. liftn 0 t k = t";
by(db.induct_tac "t" 1);
by(ALLGOALS(asm_simp_tac(addsplit(!simpset))));
qed "liftn_0";
Addsimps [liftn_0];

goal Lambda.thy "!k. liftn (Suc n) t k = lift (liftn n t k) k";
by(db.induct_tac "t" 1);
by(ALLGOALS(asm_simp_tac(addsplit(!simpset))));
by(fast_tac (HOL_cs addDs [add_lessD1]) 1);
qed "liftn_lift";
Addsimps [liftn_lift];

goal Lambda.thy "!n. substn t s n = t[liftn n s 0 / n]";
by(db.induct_tac "t" 1);
by(ALLGOALS(asm_simp_tac(addsplit(!simpset))));
qed "substn_subst_n";
Addsimps [substn_subst_n];

goal Lambda.thy "substn t s 0 = t[s/0]";
by(Simp_tac 1);
qed "substn_subst_0";
