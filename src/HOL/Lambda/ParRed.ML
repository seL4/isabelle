(*  Title:      HOL/Lambda/ParRed.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Properties of => and cd, in particular the diamond property of => and
confluence of beta.
*)

open ParRed;

Addsimps par_beta.intrs;

val par_beta_cases = map (par_beta.mk_cases db.simps)
    ["Var n => t", "Fun s => Fun t",
     "(Fun s) @ t => u", "s @ t => u", "Fun s => t"];

val parred_cs = lambda_cs addSIs par_beta.intrs addSEs par_beta_cases;

(*** beta <= par_beta <= beta^* ***)

goal ParRed.thy "(Var n => t) = (t = Var n)";
by(fast_tac parred_cs 1);
qed "par_beta_varL";
Addsimps [par_beta_varL];

goal ParRed.thy "t => t";
by(db.induct_tac "t" 1);
by(ALLGOALS Asm_simp_tac);
qed"par_beta_refl";
Addsimps [par_beta_refl];

goal ParRed.thy "beta <= par_beta";
by (rtac subsetI 1);
by (split_all_tac 1);
by (etac beta.induct 1);
by (ALLGOALS(fast_tac (parred_cs addSIs [par_beta_refl])));
qed "beta_subset_par_beta";

goal ParRed.thy "par_beta <= beta^*";
by (rtac subsetI 1);
by (split_all_tac 1);
by (etac par_beta.induct 1);
by (ALLGOALS
    (fast_tac (parred_cs addIs
	                  [rtrancl_beta_Fun,rtrancl_beta_App,rtrancl_refl,
			   rtrancl_into_rtrancl] 
                         addEs [rtrancl_trans])));
qed "par_beta_subset_beta";

(*** => ***)

goal ParRed.thy "!t' n. t => t' --> lift t n => lift t' n";
by(db.induct_tac "t" 1);
by(ALLGOALS(fast_tac (parred_cs addss (!simpset))));
qed_spec_mp "par_beta_lift";
Addsimps [par_beta_lift];

goal ParRed.thy
  "!s s' t' n. s => s' --> t => t' --> t[s/n] => t'[s'/n]";
by(db.induct_tac "t" 1);
  by(asm_simp_tac (addsplit(!simpset)) 1);
 by(strip_tac 1);
 bes par_beta_cases 1;
  by(Asm_simp_tac 1);
 by(asm_simp_tac (!simpset addsimps [subst_subst RS sym]) 1);
 by(fast_tac (parred_cs addSIs [par_beta_lift] addss (!simpset)) 1);
by(fast_tac (parred_cs addss (!simpset)) 1);
qed_spec_mp "par_beta_subst";

(*** Confluence (directly) ***)

goalw ParRed.thy [diamond_def,commute_def,square_def] "diamond(par_beta)";
by (rtac (impI RS allI RS allI) 1);
by (etac par_beta.induct 1);
by(ALLGOALS(fast_tac (parred_cs addSIs [par_beta_subst])));
qed "diamond_par_beta";


(*** cd ***)

goal ParRed.thy "!t. s => t --> t => cd s";
by(db.induct_tac "s" 1);
  by(Simp_tac 1);
 be rev_mp 1;
 by(db.induct_tac "db1" 1);
 by(ALLGOALS(fast_tac (parred_cs addSIs [par_beta_subst] addss (!simpset))));
qed_spec_mp "par_beta_cd";

(*** Confluence (via cd) ***)

goalw ParRed.thy [diamond_def,commute_def,square_def] "diamond(par_beta)";
by(fast_tac (HOL_cs addIs [par_beta_cd]) 1);
qed "diamond_par_beta2";

goal ParRed.thy "confluent(beta)";
by(fast_tac (HOL_cs addIs [diamond_par_beta2,diamond_to_confluence,
                           par_beta_subset_beta,beta_subset_par_beta]) 1);
qed"beta_confluent";
