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

val eta_cases = map (eta.mk_cases dB.simps)
    ["Abs s -e> z","s @ t -e> u","Var i -e> t"];

val beta_cases = map (beta.mk_cases dB.simps)
    ["s @ t -> u","Var i -> t"];

AddIs eta.intrs;
AddSEs (beta_cases@eta_cases);

section "eta, subst and free";

goal Eta.thy "!i t u. ~free s i --> s[t/i] = s[u/i]";
by (dB.induct_tac "s" 1);
by (ALLGOALS(simp_tac (addsplit (simpset()))));
by (Blast_tac 1);
by (Blast_tac 1);
qed_spec_mp "subst_not_free";
Addsimps [subst_not_free RS eqTrueI];

goal Eta.thy "!i k. free (lift t k) i = \
\                   (i < k & free t i | k < i & free t (pred i))";
by (dB.induct_tac "t" 1);
by (ALLGOALS(asm_full_simp_tac (addsplit (simpset()) addcongs [conj_cong])));
by (Blast_tac 2);
by(simp_tac (simpset() addsimps [pred_def] addsplits [expand_nat_case]) 1);
by (safe_tac HOL_cs);
by (ALLGOALS trans_tac);
qed "free_lift";
Addsimps [free_lift];

goal Eta.thy "!i k t. free (s[t/k]) i = \
\              (free s k & free t i | free s (if i<k then i else Suc i))";
by (dB.induct_tac "s" 1);
by (Asm_simp_tac 2);
by (Blast_tac 2);
by (asm_full_simp_tac (addsplit (simpset())) 2);
by(simp_tac (simpset() addsimps [pred_def,subst_Var]
                      addsplits [expand_if,expand_nat_case]) 1);
by (safe_tac (HOL_cs addSEs [nat_neqE]));
by (ALLGOALS trans_tac);
qed "free_subst";
Addsimps [free_subst];

goal Eta.thy "!!s. s -e> t ==> !i. free t i = free s i";
by (etac eta.induct 1);
by (ALLGOALS(asm_simp_tac (simpset() addcongs [conj_cong])));
qed_spec_mp "free_eta";

goal Eta.thy "!!s. [| s -e> t; ~free s i |] ==> ~free t i";
by (asm_simp_tac (simpset() addsimps [free_eta]) 1);
qed "not_free_eta";

goal Eta.thy "!!s. s -e> t ==> !u i. s[u/i] -e> t[u/i]";
by (etac eta.induct 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [subst_subst RS sym])));
qed_spec_mp "eta_subst";
Addsimps [eta_subst];

section "Confluence of -e>";

goalw Eta.thy [square_def,id_def]  "square eta eta (eta^=) (eta^=)";
by (rtac (impI RS allI RS allI) 1);
by (Simp_tac 1);
by (etac eta.induct 1);
by (slow_tac (claset() addIs [subst_not_free,eta_subst]
                      addIs [free_eta RS iffD1] addss simpset()) 1);
by (safe_tac (claset()));
by (blast_tac (claset() addSIs [eta_subst] addIs [free_eta RS iffD1]) 5);
by (ALLGOALS Blast_tac);
qed "square_eta";

goal Eta.thy "confluent(eta)";
by (rtac (square_eta RS square_reflcl_confluent) 1);
qed "eta_confluent";

section "Congruence rules for -e>>";

goal Eta.thy "!!s. s -e>> s' ==> Abs s -e>> Abs s'";
by (etac rtrancl_induct 1);
by (ALLGOALS(blast_tac (claset() addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_eta_Abs";

goal Eta.thy "!!s. s -e>> s' ==> s @ t -e>> s' @ t";
by (etac rtrancl_induct 1);
by (ALLGOALS(blast_tac (claset() addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_eta_AppL";

goal Eta.thy "!!s. t -e>> t' ==> s @ t -e>> s @ t'";
by (etac rtrancl_induct 1);
by (ALLGOALS(blast_tac (claset() addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_eta_AppR";

goal Eta.thy "!!s. [| s -e>> s'; t -e>> t' |] ==> s @ t -e>> s' @ t'";
by (blast_tac (claset() addSIs [rtrancl_eta_AppL, rtrancl_eta_AppR]
                       addIs [rtrancl_trans]) 1);
qed "rtrancl_eta_App";

section "Commutation of -> and -e>";

goal Eta.thy "!!s t. s -> t ==> (!i. free t i --> free s i)";
by (etac beta.induct 1);
by (ALLGOALS(Asm_full_simp_tac));
qed_spec_mp "free_beta";

goal Eta.thy "!!s t. s -> t ==> !u i. s[u/i] -> t[u/i]";
by (etac beta.induct 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [subst_subst RS sym])));
qed_spec_mp "beta_subst";
AddIs [beta_subst];

goal Eta.thy "!i. t[Var i/i] = t[Var(i)/Suc i]";
by (dB.induct_tac "t" 1);
by (ALLGOALS (asm_simp_tac (addsplit (simpset()))));
by(safe_tac (HOL_cs addSEs [nat_neqE]));
by(ALLGOALS trans_tac);
qed_spec_mp "subst_Var_Suc";
Addsimps [subst_Var_Suc];

goal Eta.thy "!!s t. s -e> t ==> (!i. lift s i -e> lift t i)";
by (etac eta.induct 1);
by (ALLGOALS(asm_simp_tac (addsplit (simpset()))));
qed_spec_mp "eta_lift";
Addsimps [eta_lift];

goal Eta.thy "!s t i. s -e> t --> u[s/i] -e>> u[t/i]";
by (dB.induct_tac "u" 1);
by (ALLGOALS(asm_simp_tac (addsplit (simpset()))));
by (blast_tac (claset() addIs [r_into_rtrancl]) 1);
by (blast_tac (claset() addSIs [rtrancl_eta_App]) 1);
by (blast_tac (claset() addSIs [rtrancl_eta_Abs,eta_lift]) 1);
qed_spec_mp "rtrancl_eta_subst";

goalw Eta.thy [square_def] "square beta eta (eta^*) (beta^=)";
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

goal Eta.thy "confluent(beta Un eta)";
by (REPEAT(ares_tac [square_rtrancl_reflcl_commute,confluent_Un,
                    beta_confluent,eta_confluent,square_beta_eta] 1));
qed "confluent_beta_eta";

section "Implicit definition of -e>: Abs(lift s 0 @ Var 0) -e> s";

goal Eta.thy "!i. (~free s i) = (? t. s = lift t i)";
by (dB.induct_tac "s" 1);
  by (simp_tac (simpset() addsplits [expand_if]) 1);
  by (SELECT_GOAL(safe_tac HOL_cs)1);
   by(etac nat_neqE 1);
    by (res_inst_tac [("x","Var nat")] exI 1);
    by (Asm_simp_tac 1);
   by (res_inst_tac [("x","Var(pred nat)")] exI 1);
   by (Asm_simp_tac 1);
  by (rtac notE 1);
   by (assume_tac 2);
  by (etac thin_rl 1);
  by (res_inst_tac [("dB","t")] dB_case_distinction 1);
    by (simp_tac (simpset() addsplits [expand_if]) 1);
    by (blast_tac (HOL_cs addDs [less_not_refl2]) 1);
   by (Simp_tac 1);
  by (Simp_tac 1);
 by (Asm_simp_tac 1);
 by (etac thin_rl 1);
 by (etac thin_rl 1);
 by (rtac allI 1);
 by (rtac iffI 1);
  by (REPEAT(eresolve_tac [conjE,exE] 1));
  by (rename_tac "u1 u2" 1);
  by (res_inst_tac [("x","u1@u2")] exI 1);
  by (Asm_simp_tac 1);
 by (etac exE 1);
 by (etac rev_mp 1);
 by (res_inst_tac [("dB","t")] dB_case_distinction 1);
   by (simp_tac (simpset() addsplits [expand_if]) 1);
  by (Simp_tac 1);
  by (Blast_tac 1);
 by (Simp_tac 1);
by (Asm_simp_tac 1);
by (etac thin_rl 1);
by (rtac allI 1);
by (rtac iffI 1);
 by (etac exE 1);
 by (res_inst_tac [("x","Abs t")] exI 1);
 by (Asm_simp_tac 1);
by (etac exE 1);
by (etac rev_mp 1);
by (res_inst_tac [("dB","t")] dB_case_distinction 1);
  by (simp_tac (simpset() addsplits [expand_if]) 1);
 by (Simp_tac 1);
by (Simp_tac 1);
by (Blast_tac 1);
qed_spec_mp "not_free_iff_lifted";

goal Eta.thy "(!s u. (~free s 0) --> R(Abs(s @ Var 0))(s[u/0])) = \
\             (!s. R(Abs(lift s 0 @ Var 0))(s))";
by (fast_tac (HOL_cs addss (simpset() addsimps [not_free_iff_lifted])) 1);
qed "explicit_is_implicit";
