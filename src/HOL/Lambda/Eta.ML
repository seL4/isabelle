(*  Title:      HOL/Lambda/Eta.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Eta reduction,
confluence of eta,
commutation of beta/eta,
confluence of beta+eta
*)

Addsimps eta.intrs;
AddIs eta.intrs;

val eta_cases = map eta.mk_cases ["Abs s -e> z", "s $ t -e> u", "Var i -e> t"];
AddSEs eta_cases;

section "eta, subst and free";

Goal "!i t u. ~free s i --> s[t/i] = s[u/i]";
by (induct_tac "s" 1);
by (ALLGOALS(simp_tac (addsplit (simpset()))));
by (Blast_tac 1);
by (Blast_tac 1);
qed_spec_mp "subst_not_free";
Addsimps [subst_not_free RS eqTrueI];

Goal "!i k. free (lift t k) i = (i < k & free t i | k < i & free t (i-1))";
by (induct_tac "t" 1);
  by (ALLGOALS(asm_full_simp_tac (addsplit (simpset()) addcongs [conj_cong])));
 by(arith_tac 1);
by(Auto_tac);
qed "free_lift";
Addsimps [free_lift];

Goal "!i k t. free (s[t/k]) i = \
\              (free s k & free t i | free s (if i<k then i else Suc i))";
by (induct_tac "s" 1);
by (Asm_simp_tac 2);
by (Blast_tac 2);
by (asm_full_simp_tac (addsplit (simpset())) 2);
by (simp_tac (simpset() addsimps [diff_Suc,subst_Var]
                      addsplits [nat.split]) 1);
by (safe_tac (HOL_cs addSEs [linorder_neqE]));
by (ALLGOALS Simp_tac);
qed "free_subst";
Addsimps [free_subst];

Goal "s -e> t ==> !i. free t i = free s i";
by (etac eta.induct 1);
by (ALLGOALS(asm_simp_tac (simpset() addcongs [conj_cong])));
qed_spec_mp "free_eta";

Goal "[| s -e> t; ~free s i |] ==> ~free t i";
by (asm_simp_tac (simpset() addsimps [free_eta]) 1);
qed "not_free_eta";

Goal "s -e> t ==> !u i. s[u/i] -e> t[u/i]";
by (etac eta.induct 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [subst_subst RS sym])));
qed_spec_mp "eta_subst";
Addsimps [eta_subst];

section "Confluence of -e>";

Goalw [square_def,id_def]  "square eta eta (eta^=) (eta^=)";
by (rtac (impI RS allI RS allI) 1);
by (Simp_tac 1);
by (etac eta.induct 1);
by (slow_tac (claset() addIs [subst_not_free,eta_subst]
                      addIs [free_eta RS iffD1] addss simpset()) 1);
by Safe_tac;
by (blast_tac (claset() addSIs [eta_subst] addIs [free_eta RS iffD1]) 5);
by (ALLGOALS Blast_tac);
qed "square_eta";

Goal "confluent(eta)";
by (rtac (square_eta RS square_reflcl_confluent) 1);
qed "eta_confluent";

section "Congruence rules for -e>>";

Goal "s -e>> s' ==> Abs s -e>> Abs s'";
by (etac rtrancl_induct 1);
by (ALLGOALS(blast_tac (claset() addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_eta_Abs";

Goal "s -e>> s' ==> s $ t -e>> s' $ t";
by (etac rtrancl_induct 1);
by (ALLGOALS(blast_tac (claset() addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_eta_AppL";

Goal "t -e>> t' ==> s $ t -e>> s $ t'";
by (etac rtrancl_induct 1);
by (ALLGOALS(blast_tac (claset() addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_eta_AppR";

Goal "[| s -e>> s'; t -e>> t' |] ==> s $ t -e>> s' $ t'";
by (blast_tac (claset() addSIs [rtrancl_eta_AppL, rtrancl_eta_AppR]
                       addIs [rtrancl_trans]) 1);
qed "rtrancl_eta_App";

section "Commutation of -> and -e>";

Goal "s -> t ==> (!i. free t i --> free s i)";
by (etac beta.induct 1);
by (ALLGOALS(Asm_full_simp_tac));
qed_spec_mp "free_beta";

Goal "s -> t ==> !u i. s[u/i] -> t[u/i]";
by (etac beta.induct 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [subst_subst RS sym])));
qed_spec_mp "beta_subst";
AddIs [beta_subst];

Goal "!i. t[Var i/i] = t[Var(i)/Suc i]";
by (induct_tac "t" 1);
by(auto_tac (claset() addSEs [linorder_neqE], addsplit (simpset())));
qed_spec_mp "subst_Var_Suc";
Addsimps [subst_Var_Suc];

Goal "s -e> t ==> (!i. lift s i -e> lift t i)";
by (etac eta.induct 1);
by (ALLGOALS(asm_simp_tac (addsplit (simpset()))));
qed_spec_mp "eta_lift";
Addsimps [eta_lift];

Goal "!s t i. s -e> t --> u[s/i] -e>> u[t/i]";
by (induct_tac "u" 1);
by (ALLGOALS(asm_simp_tac (addsplit (simpset()))));
by (blast_tac (claset() addIs [r_into_rtrancl]) 1);
by (blast_tac (claset() addSIs [rtrancl_eta_App]) 1);
by (blast_tac (claset() addSIs [rtrancl_eta_Abs,eta_lift]) 1);
qed_spec_mp "rtrancl_eta_subst";

Goalw [square_def] "square beta eta (eta^*) (beta^=)";
by (rtac (impI RS allI RS allI) 1);
by (etac beta.induct 1);
by (slow_tac (claset() addIs [r_into_rtrancl,rtrancl_eta_subst,eta_subst]
                      addss simpset()) 1);
by (blast_tac (claset() addIs [r_into_rtrancl,rtrancl_eta_AppL]) 1);
by (blast_tac (claset() addIs [r_into_rtrancl,rtrancl_eta_AppR]) 1);
(*23 seconds?*)
DelIffs dB.distinct;
Addsimps dB.distinct;
by (slow_tac (claset() addIs [r_into_rtrancl,rtrancl_eta_Abs,free_beta]
                      addss simpset()) 1);
qed "square_beta_eta";

Goal "confluent(beta Un eta)";
by (REPEAT(ares_tac [square_rtrancl_reflcl_commute,confluent_Un,
                    beta_confluent,eta_confluent,square_beta_eta] 1));
qed "confluent_beta_eta";

section "Implicit definition of -e>: Abs(lift s 0 $ Var 0) -e> s";

Goal "!i. (~free s i) = (? t. s = lift t i)";
by (induct_tac "s" 1);
  by (Simp_tac 1);
  by (SELECT_GOAL(safe_tac HOL_cs)1);
   by (etac linorder_neqE 1);
    by (res_inst_tac [("x","Var nat")] exI 1);
    by (Asm_simp_tac 1);
   by (res_inst_tac [("x","Var(nat-1)")] exI 1);
   by (Asm_simp_tac 1);
  by (rtac notE 1);
   by (assume_tac 2);
  by (etac thin_rl 1);
  by (exhaust_tac "t" 1);
    by (Asm_simp_tac 1);
   by (Asm_simp_tac 1);
  by (Asm_simp_tac 1);
 by (Asm_simp_tac 1);
 by (etac thin_rl 1);
 by (etac thin_rl 1);
 by (rtac allI 1);
 by (rtac iffI 1);
  by (REPEAT(eresolve_tac [conjE,exE] 1));
  by (rename_tac "u1 u2" 1);
  by (res_inst_tac [("x","u1$u2")] exI 1);
  by (Asm_simp_tac 1);
 by (etac exE 1);
 by (etac rev_mp 1);
 by (exhaust_tac "t" 1);
   by (Asm_simp_tac 1);
  by (Asm_simp_tac 1);
  by (Blast_tac 1);
 by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (etac thin_rl 1);
by (rtac allI 1);
by (rtac iffI 1);
 by (etac exE 1);
 by (res_inst_tac [("x","Abs t")] exI 1);
 by (Asm_simp_tac 1);
by (etac exE 1);
by (etac rev_mp 1);
by (exhaust_tac "t" 1);
  by (Asm_simp_tac 1);
 by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (Blast_tac 1);
qed_spec_mp "not_free_iff_lifted";

Goal "(!s u. (~free s 0) --> R(Abs(s $ Var 0))(s[u/0])) = \
\     (!s. R(Abs(lift s 0 $ Var 0))(s))";
by (fast_tac (HOL_cs addss (simpset() addsimps [not_free_iff_lifted])) 1);
qed "explicit_is_implicit";
