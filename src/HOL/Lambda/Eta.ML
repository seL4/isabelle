(*  Title:      HOL/Lambda/Eta.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Eta reduction,
confluence of eta,
commutation of beta/eta,
confluence of beta+eta
*)

open Eta;

Addsimps eta.intrs;

val eta_cases = map (eta.mk_cases db.simps)
    ["Fun s -e> z","s @ t -e> u","Var i -e> t"];

val beta_cases = map (beta.mk_cases db.simps)
    ["s @ t -> u","Var i -> t"];

val eta_cs = lambda_cs addIs eta.intrs
                       addSEs (beta_cases@eta_cases);

section "Arithmetic lemmas";

goal HOL.thy "!!P. P ==> P=True";
by(fast_tac HOL_cs 1);
qed "True_eq";

Addsimps [less_not_sym RS True_eq];

goal Arith.thy "i < j --> pred i < j";
by(nat_ind_tac "j" 1);
by(ALLGOALS(asm_simp_tac(simpset_of "Arith" addsimps [less_Suc_eq])));
by(nat_ind_tac "j1" 1);
by(ALLGOALS(asm_simp_tac(simpset_of "Arith")));
qed_spec_mp "less_imp_pred_less";

goal Arith.thy "i<j --> ~ pred j < i";
by(nat_ind_tac "j" 1);
by(ALLGOALS(asm_simp_tac(simpset_of "Arith" addsimps [less_Suc_eq])));
by(fast_tac (HOL_cs addDs [less_imp_pred_less]) 1);
qed_spec_mp "less_imp_not_pred_less";
Addsimps [less_imp_not_pred_less];

goal Nat.thy "i < j --> j < Suc(Suc i) --> j = Suc i";
by(nat_ind_tac "j" 1);
by(ALLGOALS(simp_tac(simpset_of "Nat")));
by(simp_tac(simpset_of "Nat" addsimps [less_Suc_eq])1);
by(fast_tac (HOL_cs addDs [less_not_sym]) 1);
qed_spec_mp "less_interval1";


section "decr and free";

goal Eta.thy "!i k. free (lift t k) i = \
\                   (i < k & free t i | k < i & free t (pred i))";
by(db.induct_tac "t" 1);
by(ALLGOALS(asm_full_simp_tac (addsplit (!simpset) addcongs [conj_cong])));
by(fast_tac HOL_cs 2);
by(safe_tac (HOL_cs addSIs [iffI]));
by (dtac Suc_mono 1);
by(ALLGOALS(Asm_full_simp_tac));
by(dtac less_trans_Suc 1 THEN atac 1);
by(dtac less_trans_Suc 2 THEN atac 2);
by(ALLGOALS(Asm_full_simp_tac));
qed "free_lift";
Addsimps [free_lift];

goal Eta.thy "!i k t. free (s[t/k]) i = \
\              (free s k & free t i | free s (if i<k then i else Suc i))";
by(db.induct_tac "s" 1);
by(ALLGOALS(asm_full_simp_tac (addsplit (!simpset) addsimps
[less_not_refl2,less_not_refl2 RS not_sym])));
by(fast_tac HOL_cs 2);
by(safe_tac (HOL_cs addSIs [iffI]));
by(ALLGOALS(Asm_simp_tac));
by(fast_tac (HOL_cs addEs [less_imp_not_pred_less RS notE]) 1);
by(fast_tac (HOL_cs addDs [less_not_sym]) 1);
by (dtac Suc_mono 1);
by(dtac less_interval1 1 THEN atac 1);
by(asm_full_simp_tac (simpset_of "Nat" addsimps [eq_sym_conv]) 1);
by(dtac less_trans_Suc 1 THEN atac 1);
by(Asm_full_simp_tac 1);
qed "free_subst";
Addsimps [free_subst];

goal Eta.thy "!!s. s -e> t ==> !i. free t i = free s i";
by (etac eta.induct 1);
by(ALLGOALS(asm_simp_tac (!simpset addsimps [decr_def] addcongs [conj_cong])));
qed_spec_mp "free_eta";

goal Eta.thy "!!s. [| s -e> t; ~free s i |] ==> ~free t i";
by(asm_simp_tac (!simpset addsimps [free_eta]) 1);
qed "not_free_eta";

goal Eta.thy "!i t u. ~free s i --> s[t/i] = s[u/i]";
by(db.induct_tac "s" 1);
by(ALLGOALS(simp_tac (addsplit (!simpset))));
by(fast_tac HOL_cs 1);
by(fast_tac HOL_cs 1);
qed_spec_mp "subst_not_free";

goalw Eta.thy [decr_def] "!!s. ~free s i ==> s[t/i] = decr s i";
by (etac subst_not_free 1);
qed "subst_decr";

goal Eta.thy "!!s. s -e> t ==> !u i. s[u/i] -e> t[u/i]";
by (etac eta.induct 1);
by(ALLGOALS(asm_simp_tac (!simpset addsimps [subst_subst RS sym,decr_def])));
by(asm_simp_tac (!simpset addsimps [subst_decr]) 1);
qed_spec_mp "eta_subst";
Addsimps [eta_subst];

goalw Eta.thy [decr_def] "!!s. s -e> t ==> decr s i -e> decr t i";
by (etac eta_subst 1);
qed "eta_decr";

section "Confluence of -e>";

goalw Eta.thy [square_def,id_def]  "square eta eta (eta^=) (eta^=)";
by (rtac (impI RS allI RS allI) 1);
by (etac eta.induct 1);
by(ALLGOALS(fast_tac (eta_cs addSEs [eta_decr,not_free_eta] addss !simpset)));
val lemma = result();

goal Eta.thy "confluent(eta)";
by(rtac (lemma RS square_reflcl_confluent) 1);
qed "eta_confluent";

section "Congruence rules for -e>>";

goal Eta.thy "!!s. s -e>> s' ==> Fun s -e>> Fun s'";
by (etac rtrancl_induct 1);
by (ALLGOALS(fast_tac (eta_cs addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_eta_Fun";

goal Eta.thy "!!s. s -e>> s' ==> s @ t -e>> s' @ t";
by (etac rtrancl_induct 1);
by (ALLGOALS(fast_tac (eta_cs addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_eta_AppL";

goal Eta.thy "!!s. t -e>> t' ==> s @ t -e>> s @ t'";
by (etac rtrancl_induct 1);
by (ALLGOALS(fast_tac (eta_cs addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_eta_AppR";

goal Eta.thy "!!s. [| s -e>> s'; t -e>> t' |] ==> s @ t -e>> s' @ t'";
by (fast_tac (eta_cs addSIs [rtrancl_eta_AppL,rtrancl_eta_AppR]
                     addIs [rtrancl_trans]) 1);
qed "rtrancl_eta_App";

section "Commutation of -> and -e>";

goal Eta.thy "!!s t. s -> t ==> (!i. free t i --> free s i)";
by (etac beta.induct 1);
by(ALLGOALS(Asm_full_simp_tac));
qed_spec_mp "free_beta";

goalw Eta.thy [decr_def] "!!s t. s -> t ==> (!i. decr s i -> decr t i)";
by (etac beta.induct 1);
by(ALLGOALS(asm_full_simp_tac (!simpset addsimps [subst_subst RS sym])));
qed_spec_mp "beta_decr";

goalw Eta.thy [decr_def]
  "decr (Var i) k = (if i<=k then Var i else Var(pred i))";
by(simp_tac (addsplit (!simpset) addsimps [le_def]) 1);
qed "decr_Var";
Addsimps [decr_Var];

goalw Eta.thy [decr_def] "decr (s@t) i = (decr s i)@(decr t i)";
by(Simp_tac 1);
qed "decr_App";
Addsimps [decr_App];

goalw Eta.thy [decr_def] "decr (Fun s) i = Fun (decr s (Suc i))";
by(Simp_tac 1);
qed "decr_Fun";
Addsimps [decr_Fun];

goal Eta.thy "!i. ~free t (Suc i) --> decr t i = decr t (Suc i)";
by(db.induct_tac "t" 1);
by(ALLGOALS(asm_simp_tac (addsplit (!simpset) addsimps [le_def, less_Suc_eq])));
by(fast_tac HOL_cs 1);
qed "decr_not_free";
Addsimps [decr_not_free];

goal Eta.thy "!!s t. s -e> t ==> (!i. lift s i -e> lift t i)";
by (etac eta.induct 1);
by(ALLGOALS(asm_simp_tac (addsplit (!simpset) addsimps [decr_def])));
by(asm_simp_tac (addsplit (!simpset) addsimps [subst_decr]) 1);
qed_spec_mp "eta_lift";
Addsimps [eta_lift];

goal Eta.thy "!s t i. s -e> t --> u[s/i] -e>> u[t/i]";
by(db.induct_tac "u" 1);
by(ALLGOALS(asm_simp_tac (addsplit (!simpset))));
by(fast_tac (eta_cs addIs [r_into_rtrancl]) 1);
by(fast_tac (eta_cs addSIs [rtrancl_eta_App]) 1);
by(fast_tac (eta_cs addSIs [rtrancl_eta_Fun,eta_lift]) 1);
qed_spec_mp "rtrancl_eta_subst";

goalw Eta.thy [square_def] "square beta eta (eta^*) (beta^=)";
by (rtac (impI RS allI RS allI) 1);
by (etac beta.induct 1);
by(strip_tac 1);
by (eresolve_tac eta_cases 1);
by (eresolve_tac eta_cases 1);
by(fast_tac (eta_cs addss (!simpset addsimps [subst_decr])) 1);
by(fast_tac (eta_cs addIs [r_into_rtrancl,eta_subst]) 1);
by(fast_tac (eta_cs addIs [rtrancl_eta_subst]) 1);
by(fast_tac (eta_cs addIs [r_into_rtrancl,rtrancl_eta_AppL]) 1);
by(fast_tac (eta_cs addIs [r_into_rtrancl,rtrancl_eta_AppR]) 1);
by(fast_tac (eta_cs addIs [r_into_rtrancl,rtrancl_eta_Fun,free_beta,beta_decr]
                  addss (!simpset addsimps[subst_decr,symmetric decr_def])) 1);
qed "square_beta_eta";

goal Eta.thy "confluent(beta Un eta)";
by(REPEAT(ares_tac [square_rtrancl_reflcl_commute,confluent_Un,
                    beta_confluent,eta_confluent,square_beta_eta] 1));
qed "confluent_beta_eta";


section "Implicit definition of -e>: Fun(lift s 0 @ Var 0) -e> s";

goal Eta.thy "!i. (~free s i) = (? t. s = lift t i)";
by(db.induct_tac "s" 1);
  by(simp_tac (!simpset setloop (split_tac [expand_if])) 1);
  by(SELECT_GOAL(safe_tac HOL_cs)1);
   by(res_inst_tac [("m","nat"),("n","i")] nat_less_cases 1);
     by(res_inst_tac [("x","Var nat")] exI 1);
     by(Asm_simp_tac 1);
    by(fast_tac HOL_cs 1);
   by(res_inst_tac [("x","Var(pred nat)")] exI 1);
   by(Asm_simp_tac 1);
  br notE 1;
   ba 2;
  be thin_rl 1;
  by(res_inst_tac [("db","t")] db_case_distinction 1);
    by(simp_tac (!simpset setloop (split_tac [expand_if])) 1);
    by(fast_tac (HOL_cs addDs [less_not_refl2]) 1);
   by(Simp_tac 1);
  by(Simp_tac 1);
 by(asm_simp_tac (!simpset addsimps [de_Morgan_disj]) 1);
 be thin_rl 1;
 be thin_rl 1;
 br allI 1;
 br iffI 1;
  by(REPEAT(eresolve_tac [conjE,exE] 1));
  by(rename_tac "u1 u2" 1);
  by(res_inst_tac [("x","u1@u2")] exI 1);
  by(Asm_simp_tac 1);
 be exE 1;
 be rev_mp 1;
 by(res_inst_tac [("db","t")] db_case_distinction 1);
   by(simp_tac (!simpset setloop (split_tac [expand_if])) 1);
  by(Simp_tac 1);
  by(fast_tac HOL_cs 1);
 by(Simp_tac 1);
by(Asm_simp_tac 1);
be thin_rl 1;
br allI 1;
br iffI 1;
 be exE 1;
 by(res_inst_tac [("x","Fun t")] exI 1);
 by(Asm_simp_tac 1);
be exE 1;
be rev_mp 1;
by(res_inst_tac [("db","t")] db_case_distinction 1);
  by(simp_tac (!simpset setloop (split_tac [expand_if])) 1);
 by(Simp_tac 1);
by(Simp_tac 1);
by(fast_tac HOL_cs 1);
qed_spec_mp "not_free_iff_lifted";

goalw Eta.thy [decr_def]
 "(!s. (~free s 0) --> R(Fun(s @ Var 0))(decr s 0)) = \
\ (!s. R(Fun(lift s 0 @ Var 0))(s))";
by(fast_tac (HOL_cs addss (!simpset addsimps [lemma,not_free_iff_lifted])) 1);
qed "explicit_is_implicit";
