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

(*** Arithmetic lemmas ***)

goal HOL.thy "!!P. P ==> P=True";
by(fast_tac HOL_cs 1);
qed "True_eq";

Addsimps [less_not_sym RS True_eq];

goal Arith.thy "i < j --> pred i < j";
by(nat_ind_tac "j" 1);
by(ALLGOALS(asm_simp_tac(simpset_of "Arith")));
by(nat_ind_tac "j1" 1);
by(ALLGOALS(asm_simp_tac(simpset_of "Arith")));
bind_thm("less_imp_pred_less",result() RS mp);

goal Arith.thy "i<j --> ~ pred j < i";
by(nat_ind_tac "j" 1);
by(ALLGOALS(asm_simp_tac(simpset_of "Arith")));
by(fast_tac (HOL_cs addDs [less_imp_pred_less]) 1);
bind_thm("less_imp_not_pred_less", result() RS mp);
Addsimps [less_imp_not_pred_less];

goal Nat.thy "i < j --> j < Suc(Suc i) --> j = Suc i";
by(nat_ind_tac "j" 1);
by(ALLGOALS(simp_tac(simpset_of "Nat")));
by(fast_tac (HOL_cs addDs [less_not_sym]) 1);
bind_thm("less_interval1", result() RS mp RS mp);


(*** decr and free ***)

goal Eta.thy "!i k. free (lift t k) i = \
\                   (i < k & free t i | k < i & free t (pred i))";
by(db.induct_tac "t" 1);
by(ALLGOALS(asm_full_simp_tac (addsplit (!simpset) addcongs [conj_cong])));
by(fast_tac HOL_cs 2);
by(safe_tac (HOL_cs addSIs [iffI]));
bd Suc_mono 1;
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
bd Suc_mono 1;
by(dtac less_interval1 1 THEN atac 1);
by(asm_full_simp_tac (simpset_of "Nat" addsimps [eq_sym_conv]) 1);
by(dtac less_trans_Suc 1 THEN atac 1);
by(Asm_full_simp_tac 1);
qed "free_subst";
Addsimps [free_subst];

goal Eta.thy "!!s. s -e> t ==> !i. free t i = free s i";
be (eta.mutual_induct RS spec RS spec RSN (2,rev_mp)) 1;
by(ALLGOALS(asm_simp_tac (!simpset addsimps [decr_def] addcongs [conj_cong])));
bind_thm("free_eta",result() RS spec);

goal Eta.thy "!!s. [| s -e> t; ~free s i |] ==> ~free t i";
by(asm_simp_tac (!simpset addsimps [free_eta]) 1);
qed "not_free_eta";

goal Eta.thy "!i t u. ~free s i --> s[t/i] = s[u/i]";
by(db.induct_tac "s" 1);
by(ALLGOALS(simp_tac (addsplit (!simpset))));
by(fast_tac HOL_cs 1);
by(fast_tac HOL_cs 1);
bind_thm("subst_not_free", result() RS spec RS spec RS spec RS mp);

goalw Eta.thy [decr_def] "!!s. ~free s i ==> s[t/i] = decr s i";
be subst_not_free 1;
qed "subst_decr";

goal Eta.thy "!!s. s -e> t ==> !u i. s[u/i] -e> t[u/i]";
be (eta.mutual_induct RS spec RS spec RSN (2,rev_mp)) 1;
by(ALLGOALS(asm_simp_tac (!simpset addsimps [subst_subst RS sym,decr_def])));
by(asm_simp_tac (!simpset addsimps [subst_decr]) 1);
bind_thm("eta_subst",result() RS spec RS spec);
Addsimps [eta_subst];

goalw Eta.thy [decr_def] "!!s. s -e> t ==> decr s i -e> decr t i";
be eta_subst 1;
qed "eta_decr";

(*** Confluence of eta ***)

goalw Eta.thy [id_def]
  "!x y. x-e> y --> (!z. x-e>z --> (? u. y -e>= u & z -e>= u))";
br eta.mutual_induct 1;
by(ALLGOALS(fast_tac (eta_cs addSEs [eta_decr,not_free_eta] addss !simpset)));
val lemma = result() RS spec RS spec RS mp RS spec RS mp;

goalw Eta.thy [diamond_def,commute_def,square_def] "diamond(eta^=)";
by(fast_tac (eta_cs addEs [lemma]) 1);
qed "diamond_refl_eta";

goal Eta.thy "confluent(eta)";
by(stac (rtrancl_reflcl RS sym) 1);
by(rtac (diamond_refl_eta RS diamond_confluent) 1);
qed "eta_confluent";

(*** Congruence rules for ->> ***)

goal Eta.thy "!!s. s -e>> s' ==> Fun s -e>> Fun s'";
be rtrancl_induct 1;
by (ALLGOALS(fast_tac (eta_cs addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_eta_Fun";

goal Eta.thy "!!s. s -e>> s' ==> s @ t -e>> s' @ t";
be rtrancl_induct 1;
by (ALLGOALS(fast_tac (eta_cs addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_eta_AppL";

goal Eta.thy "!!s. t -e>> t' ==> s @ t -e>> s @ t'";
be rtrancl_induct 1;
by (ALLGOALS(fast_tac (eta_cs addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_eta_AppR";

goal Eta.thy "!!s. [| s -e>> s'; t -e>> t' |] ==> s @ t -e>> s' @ t'";
by (fast_tac (eta_cs addSIs [rtrancl_eta_AppL,rtrancl_eta_AppR]
                     addIs [rtrancl_trans]) 1);
qed "rtrancl_eta_App";

(*** Commutation of beta and eta ***)

goal Eta.thy "!!s. s -> t ==> !i. free t i --> free s i";
be (beta.mutual_induct RS spec RS spec RSN (2,rev_mp)) 1;
by(ALLGOALS(Asm_full_simp_tac));
bind_thm("free_beta", result() RS spec RS mp);

goalw Eta.thy [decr_def] "!s t. s -> t --> (!i. decr s i -> decr t i)";
br beta.mutual_induct 1;
by(ALLGOALS(asm_full_simp_tac (!simpset addsimps [subst_subst RS sym])));
bind_thm("beta_decr", result() RS spec RS spec RS mp RS spec);

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
by(ALLGOALS(asm_simp_tac (addsplit (!simpset) addsimps [le_def])));
by(fast_tac (HOL_cs addDs [less_interval1]) 1);
by(fast_tac HOL_cs 1);
qed "decr_not_free";
Addsimps [decr_not_free];

goal Eta.thy "!s t. s -e> t --> (!i. lift s i -e> lift t i)";
br eta.mutual_induct 1;
by(ALLGOALS(asm_simp_tac (addsplit (!simpset) addsimps [decr_def])));
by(asm_simp_tac (addsplit (!simpset) addsimps [subst_decr]) 1);
bind_thm("eta_lift",result() RS spec RS spec RS mp RS spec);
Addsimps [eta_lift];

goal Eta.thy "!s t i. s -e> t --> u[s/i] -e>> u[t/i]";
by(db.induct_tac "u" 1);
by(ALLGOALS(asm_simp_tac (addsplit (!simpset))));
by(fast_tac (eta_cs addIs [r_into_rtrancl]) 1);
by(fast_tac (eta_cs addSIs [rtrancl_eta_App]) 1);
by(fast_tac (eta_cs addSIs [rtrancl_eta_Fun,eta_lift]) 1);
bind_thm("rtrancl_eta_subst", result() RS spec RS spec RS spec RS mp);

goalw Eta.thy [square_def] "square beta eta (eta^*) (beta^=)";
br beta.mutual_induct 1;
by(strip_tac 1);
bes eta_cases 1;
bes eta_cases 1;
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
