(*** Every term in IT terminates ***)

Goal "s : termi beta ==> !t. t : termi beta --> \
\     (!r ss. t = r[s/0]$$ss --> Abs r $ s $$ ss : termi beta)";
be acc_induct 1;
be thin_rl 1;
br allI 1;
br impI 1;
be acc_induct 1;
by(Clarify_tac 1);
br accI 1;
by(safe_tac (claset() addSEs [apps_betasE]));
   ba 1;
  by(blast_tac (claset() addIs [subst_preserves_beta,apps_preserves_beta]) 1);
 by(blast_tac (claset()
    addIs [apps_preserves_beta2,subst_preserves_beta2,rtrancl_converseI]
    addDs [acc_downwards]) 1);
(* FIXME: acc_downwards can be replaced by acc(R ^* ) = acc(r) *)
by(blast_tac (claset() addDs [apps_preserves_betas]) 1);
qed_spec_mp "double_induction_lemma";

Goal "t : IT ==> t : termi(beta)";
be IT.induct 1;
  bd rev_subsetD 1;
   br lists_mono 1;
   br Int_lower2 1;
  by(Asm_full_simp_tac 1);
  bd lists_accD 1;
  be acc_induct 1;
  br accI 1;
  by(blast_tac (claset() addSDs [head_Var_reduction]) 1);
 be acc_induct 1;
 br accI 1;
 by(Blast_tac 1);
by(blast_tac (claset() addIs [double_induction_lemma]) 1);
qed "IT_implies_termi";

(*** Every terminating term is in IT ***)

val IT_cases = map (IT.mk_cases
 ([Var_apps_eq_Var_apps_conv, Abs_eq_apps_conv, apps_eq_Abs_conv,
   Abs_apps_eq_Abs_apps_conv,
   Var_apps_neq_Abs_apps, Var_apps_neq_Abs_apps RS not_sym,
   hd(tl(get_thms List.thy "foldl.simps")) RS sym ]
  @ dB.simps @ list.simps))
    ["Var n $$ ss : IT", "Abs t : IT", "Abs r $ s $$ ts : IT"];
AddSEs IT_cases;

Goal "t : termi beta ==> \
\     !r rs. t = r$$rs --> r : termi beta & rs : termi(step1 beta)";
be acc_induct 1;
by(force_tac (claset()
     addIs [apps_preserves_beta,apps_preserves_betas,accI],simpset()) 1);
val lemma = result();

Goal "r$$rs : termi beta ==> r : termi beta & rs : termi(step1 beta)";
bd lemma 1;
by(Blast_tac 1);
qed "apps_in_termi_betaD";

Goal "t : termi beta ==> !r. t = Abs r --> r : termi beta";
be acc_induct 1;
by(force_tac (claset() addIs [accI],simpset()) 1);
val lemma = result();

Goal "Abs r : termi beta ==> r : termi beta";
bd lemma 1;
by(Blast_tac 1);
qed "Abs_in_termi_betaD";

Goal "t : termi beta ==> !r s. t = r$s --> r : termi beta & s : termi beta";
be acc_induct 1;
by(force_tac (claset() addIs [accI],simpset()) 1);
val lemma = result();

Goal "r$s : termi beta ==> r : termi beta & s : termi beta";
bd lemma 1;
by(Blast_tac 1);
qed "App_in_termi_betaD";


Goal "r : termi beta ==> r : IT";
be acc_induct 1;
by(rename_tac "r" 1);
be rev_mp 1;
be rev_mp 1;
by(Simp_tac 1);
by(res_inst_tac [("t","r")] Apps_dB_induct 1);
 by(rename_tac "n ts" 1);
 by(Clarify_tac 1);
 brs IT.intrs 1;
 by(Clarify_tac 1);
 by(EVERY1[dtac bspec, atac]);
 by(EVERY[etac impE 1, etac mp 2]);
  by(Clarify_tac 1);
  bd converseI 1;
  by(EVERY1[dtac ex_step1I, atac]);
  by(Clarify_tac 1);
  by(rename_tac "us" 1);
  by(eres_inst_tac [("x","Var n $$ us")] allE 1);
  by(Force_tac 1);
 bd apps_in_termi_betaD 1;
 by(asm_full_simp_tac (simpset() delsimps [step1_converse]
                                 addsimps [step1_converse RS sym]) 1);
 by(blast_tac (claset() addDs [lists_accI]) 1);
by(rename_tac "u ts" 1);
by(exhaust_tac "ts" 1);
 by(Asm_full_simp_tac 1);
 by(Clarify_tac 1);
 brs IT.intrs 1;
 by(blast_tac (claset() addDs [Abs_in_termi_betaD]) 1);
by(rename_tac "s ss" 1);
by(Asm_full_simp_tac 1);
by(Clarify_tac 1);
brs IT.intrs 1;
 by(blast_tac (claset() addIs [apps_preserves_beta]) 1);
by(EVERY[etac impE 1, etac mp 2]);
 by(Clarify_tac 1);
 by(rename_tac "t" 1);
 by(eres_inst_tac [("x","Abs u $ t $$ ss")] allE 1);
 by(Force_tac 1);
by(blast_tac (claset() addSDs [apps_in_termi_betaD, App_in_termi_betaD]) 1);
qed "termi_implies_IT";
