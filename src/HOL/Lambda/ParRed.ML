(*  Title:      HOL/Lambda/ParRed.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Properties of => and cd, in particular the diamond property of => and
confluence of beta.
*)

open ParRed;

val parred_ss = lambda_ss addsimps
  par_beta.intrs @ [cd_Var,cd_Fun];

val par_beta_cases = map (par_beta.mk_cases db.simps)
    ["Var n => t", "Fun s => Fun t",
     "(Fun s) @ t => u", "s @ t => u", "Fun s => t"];

val parred_cs = lambda_cs addSIs par_beta.intrs addSEs par_beta_cases;

(*** beta <= par_beta <= beta^* ***)

goal ParRed.thy "(Var n => t) = (t = Var n)";
by(fast_tac parred_cs 1);
qed "par_beta_varL";
val parred_ss = parred_ss addsimps [par_beta_varL];

goal ParRed.thy "t => t";
by(db.induct_tac "t" 1);
by(ALLGOALS(asm_simp_tac parred_ss));
qed"par_beta_refl";
val parred_ss = parred_ss addsimps [par_beta_refl];

goal ParRed.thy "beta <= par_beta";
br subsetI 1;
by (res_inst_tac[("p","x")]PairE 1);
by (hyp_subst_tac 1);
be (beta.mutual_induct RS spec RS spec RSN (2,rev_mp)) 1;
by (ALLGOALS(fast_tac (parred_cs addSIs [par_beta_refl])));
qed "beta_subset_par_beta";

goal ParRed.thy "par_beta <= beta^*";
br subsetI 1;
by (res_inst_tac[("p","x")]PairE 1);
by (hyp_subst_tac 1);
be (par_beta.mutual_induct RS spec RS spec RSN (2,rev_mp)) 1;
by (ALLGOALS(fast_tac (parred_cs addIs
       [rtrancl_beta_Fun,rtrancl_beta_App,rtrancl_refl,
        rtrancl_into_rtrancl] addEs [rtrancl_trans])));
qed "par_beta_subset_beta";

(*** => ***)

goal ParRed.thy "!t' n. t => t' --> lift t n => lift t' n";
by(db.induct_tac "t" 1);
by(ALLGOALS(fast_tac (parred_cs addss parred_ss)));
bind_thm("par_beta_lift", result() RS spec RS spec RS mp);
val parred_ss = parred_ss addsimps [par_beta_lift];

goal ParRed.thy
  "!s s' t' n. s => s' --> t => t' --> t[s/n] => t'[s'/n]";
by(db.induct_tac "t" 1);
  by(asm_simp_tac (addsplit parred_ss) 1);
 by(strip_tac 1);
 bes par_beta_cases 1;
  by(asm_simp_tac parred_ss 1);
 by(asm_simp_tac parred_ss 1);
 br (zero_less_Suc RS subst_subst RS subst) 1;
 by(fast_tac (parred_cs addSIs [par_beta_lift] addss parred_ss) 1);
by(fast_tac (parred_cs addss parred_ss) 1);
bind_thm("par_beta_subst",
         result()  RS spec RS spec RS spec RS spec RS mp RS mp);

(*** Confluence (directly) ***)

goalw ParRed.thy [diamond_def] "diamond(par_beta)";
by(REPEAT(rtac allI 1));
br impI 1;
be (par_beta.mutual_induct RS spec RS spec RSN (2,rev_mp)) 1;
by(ALLGOALS(fast_tac (parred_cs addSIs [par_beta_subst])));
qed "diamond_par_beta";


(*** cd ***)

goal ParRed.thy "cd(Var n @ t) = Var n @ cd t";
by(simp_tac (parred_ss addsimps [cd_App]) 1);
qed"cd_App_Var";

goal ParRed.thy "cd((r @ s) @ t) = cd(r @ s) @ cd t";
by(simp_tac (parred_ss addsimps [cd_App]) 1);
qed"cd_App_App";

goal ParRed.thy "cd((Fun s) @ t) = (cd s)[cd t/0]";
by(simp_tac (parred_ss addsimps [cd_App,deFun_Fun]) 1);
qed"cd_App_Fun";

val parred_ss = parred_ss addsimps [cd_App_Var,cd_App_App,cd_App_Fun];

goal ParRed.thy "!t. s => t --> t => cd s";
by(db.induct_tac "s" 1);
  by(simp_tac parred_ss 1);
 be rev_mp 1;
 by(db.induct_tac "db1" 1);
 by(ALLGOALS(fast_tac (parred_cs addSIs [par_beta_subst] addss parred_ss)));
bind_thm("par_beta_cd", result() RS spec RS mp);

(*** Confluence (via cd) ***)

goalw ParRed.thy [diamond_def] "diamond(par_beta)";
by(fast_tac (HOL_cs addIs [par_beta_cd]) 1);
qed "diamond_par_beta";

goal ParRed.thy "confluent(beta)";
by(fast_tac (HOL_cs addIs [diamond_par_beta,diamond_to_confluence,
                           par_beta_subset_beta,beta_subset_par_beta]) 1);
qed"beta_confluent";
