(*  Title:      HOL/Lambda/ListBeta.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen
*)

Goal
 "v -> v' ==> !rs. v = (Var n)$$rs --> (? ss. rs => ss & v' = (Var n)$$ss)";
by (etac beta.induct 1);
   by (Asm_full_simp_tac 1);
  by (rtac allI 1);
  by (res_inst_tac [("xs","rs")] rev_exhaust 1);
   by (Asm_full_simp_tac 1);
  by (force_tac (claset() addIs [append_step1I],simpset()) 1);
 by (rtac allI 1);
 by (res_inst_tac [("xs","rs")] rev_exhaust 1);
  by (Asm_full_simp_tac 1);
 by (mk_auto_tac (claset() addIs [disjI2 RS append_step1I],simpset()) 0 3);
val lemma = result();

Goal "(Var n)$$rs -> v ==> (? ss. rs => ss & v = (Var n)$$ss)";
by (dtac lemma 1);
by (Blast_tac 1);
qed "head_Var_reduction";

Goal "u -> u' ==> !r rs. u = r$$rs --> \
\     ( (? r'. r -> r' & u' = r'$$rs) | \
\       (? rs'. rs => rs' & u' = r$$rs') | \
\       (? s t ts. r = Abs s & rs = t#ts & u' = s[t/0]$$ts))";
by (etac beta.induct 1);
   by (clarify_tac (claset() delrules [disjCI]) 1);
   by (case_tac "r" 1);
     by (Asm_full_simp_tac 1);
    by (asm_full_simp_tac (simpset() addsimps [App_eq_foldl_conv]) 1);
    by (split_asm_tac [split_if_asm] 1);
     by (Asm_full_simp_tac 1);
     by (Blast_tac 1);
    by (Asm_full_simp_tac 1);
   by (asm_full_simp_tac (simpset() addsimps [App_eq_foldl_conv]) 1);
   by (split_asm_tac [split_if_asm] 1);
    by (Asm_full_simp_tac 1);
   by (Asm_full_simp_tac 1);
  by (clarify_tac (claset() delrules [disjCI]) 1);
  by (dtac (App_eq_foldl_conv RS iffD1) 1);
  by (split_asm_tac [split_if_asm] 1);
   by (Asm_full_simp_tac 1);
   by (Blast_tac 1);
  by (force_tac (claset() addIs [disjI1 RS append_step1I],simpset()) 1);
 by (clarify_tac (claset() delrules [disjCI]) 1);
 by (dtac (App_eq_foldl_conv RS iffD1) 1);
 by (split_asm_tac [split_if_asm] 1);
  by (Asm_full_simp_tac 1);
  by (Blast_tac 1);
 by (mk_auto_tac (claset() addIs [disjI2 RS append_step1I],simpset()) 0 3);
val lemma = result();

val major::prems =
Goal "[| r $$ rs -> s; !!r'. [| r -> r'; s = r' $$ rs |] ==> R;   \
\        !!rs'. [| rs => rs'; s = r $$ rs' |] ==> R;              \
\        !!t u us. [| r = Abs t; rs = u # us; s = t[u/0] $$ us |] ==> R |]   \
\     ==> R";
by (cut_facts_tac [major RS lemma RS spec RS spec] 1);
by (REPEAT_FIRST (ares_tac [refl] ORELSE'
		  eresolve_tac (prems @ [exE, conjE, impE, disjE])));
qed "apps_betasE";
AddSEs [apps_betasE];

Goal "r -> s ==> r$$ss -> s$$ss";
by (rev_induct_tac "ss" 1);
by (Auto_tac);
qed "apps_preserves_beta";
Addsimps [apps_preserves_beta];

Goal "r ->> s ==> r$$ss ->> s$$ss";
by (etac rtrancl_induct 1);
 by (Blast_tac 1);
by (blast_tac (claset() addIs [apps_preserves_beta,rtrancl_into_rtrancl]) 1);
qed "apps_preserves_beta2";
Addsimps [apps_preserves_beta2];

Goal "!ss. rs => ss --> r$$rs -> r$$ss";
by (rev_induct_tac "rs" 1);
 by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (res_inst_tac [("xs","ss")] rev_exhaust 1);
 by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (dtac Snoc_step1_SnocD 1);
by (Blast_tac 1);
qed_spec_mp "apps_preserves_betas";
Addsimps [apps_preserves_betas];
