(*  Title:      HOL/Lambda/InductTermi.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen
*)

(*** Every term in IT terminates ***)

Goal "s : termi beta ==> !t. t : termi beta --> \
\     (!r ss. t = r[s/0]$$ss --> Abs r $ s $$ ss : termi beta)";
by (etac acc_induct 1);
by (etac thin_rl 1);
by (rtac allI 1);
by (rtac impI 1);
by (etac acc_induct 1);
by (Clarify_tac 1);
by (rtac accI 1);
by (safe_tac (claset() addSEs [apps_betasE]));
   by (assume_tac 1);
  by (blast_tac (claset() addIs [subst_preserves_beta,apps_preserves_beta]) 1);
 by (blast_tac (claset()
    addIs [apps_preserves_beta2,subst_preserves_beta2,rtrancl_converseI]
    addDs [acc_downwards]) 1);
(* FIXME: acc_downwards can be replaced by acc(R ^* ) = acc(r) *)
by (blast_tac (claset() addDs [apps_preserves_betas]) 1);
qed_spec_mp "double_induction_lemma";

Goal "t : IT ==> t : termi(beta)";
by (etac IT.induct 1);
  by (dtac rev_subsetD 1);
   by (rtac lists_mono 1);
   by (rtac Int_lower2 1);
  by (Asm_full_simp_tac 1);
  by (dtac lists_accD 1);
  by (etac acc_induct 1);
  by (rtac accI 1);
  by (blast_tac (claset() addSDs [head_Var_reduction]) 1);
 by (etac acc_induct 1);
 by (rtac accI 1);
 by (Blast_tac 1);
by (blast_tac (claset() addIs [double_induction_lemma]) 1);
qed "IT_implies_termi";

(*** Every terminating term is in IT ***)

Addsimps [Var_apps_neq_Abs_apps RS not_sym];

Goal "Var n $$ ss ~= Abs r $ s $$ ts";
by (simp_tac (simpset() addsimps [foldl_Cons RS sym] 
	                delsimps [foldl_Cons]) 1);
qed "Var_apps_neq_Abs_app_apps";
Addsimps [Var_apps_neq_Abs_app_apps,
	  Var_apps_neq_Abs_app_apps RS not_sym];


Goal "(Abs r $ s $$ ss = Abs r' $ s' $$ ss') = (r=r' & s=s' & ss=ss')";
by (simp_tac (simpset() addsimps [foldl_Cons RS sym] 
	                delsimps [foldl_Cons]) 1);
qed "Abs_apps_eq_Abs_app_apps";
Addsimps [Abs_apps_eq_Abs_app_apps];

val IT_cases = 
    map IT.mk_cases
        ["Var n $$ ss : IT", "Abs t : IT", "Abs r $ s $$ ts : IT"];
AddSEs IT_cases;


Goal "r : termi beta ==> r : IT";
by (etac acc_induct 1);
by (rename_tac "r" 1);
by (etac thin_rl 1);
by (etac rev_mp 1);
by (Simp_tac 1);
by (res_inst_tac [("t","r")] Apps_dB_induct 1);
 by (rename_tac "n ts" 1);
 by (Clarify_tac 1);
 by (resolve_tac IT.intrs 1);
 by (Clarify_tac 1);
 by (EVERY1[dtac bspec, atac]);
 by (etac mp 1);
  by (Clarify_tac 1);
  by (dtac converseI 1);
  by (EVERY1[dtac ex_step1I, atac]);
  by (Clarify_tac 1);
  by (rename_tac "us" 1);
  by (eres_inst_tac [("x","Var n $$ us")] allE 1);
  by (Force_tac 1);
by (rename_tac "u ts" 1);
by (cases_tac "ts" 1);
 by (Asm_full_simp_tac 1);
 by (blast_tac (claset() addIs IT.intrs) 1);
by (rename_tac "s ss" 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (resolve_tac IT.intrs 1);
 by (blast_tac (claset() addIs [apps_preserves_beta]) 1);
by (etac mp 1);
 by (Clarify_tac 1);
 by (rename_tac "t" 1);
 by (eres_inst_tac [("x","Abs u $ t $$ ss")] allE 1);
 by (Force_tac 1);
qed "termi_implies_IT";
