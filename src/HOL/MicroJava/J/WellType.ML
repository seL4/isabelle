(*  Title:      HOL/MicroJava/J/WellType.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

Goal
"[| method (G,C) sig = Some (md,rT,b); wf_prog wf_mb G; G\\<turnstile>T''\\<preceq>C C|]\
\ ==> \\<exists>md' rT' b'. method (G,T'') sig = Some (md',rT',b') \\<and> G\\<turnstile>rT'\\<preceq>rT";
by( dtac subcls_widen_methd 1);
by   Auto_tac;
qed "widen_methd";


Goal
"[|method (G,C) sig = Some (md,rT,b); G\\<turnstile>T''\\<preceq>C C; wf_prog wf_mb G; \
\ class G C = Some y|] ==> \\<exists>T' rT' b. method (G,T'') sig = Some (T',rT',b) \\<and> \
\ G\\<turnstile>rT'\\<preceq>rT \\<and> G\\<turnstile>T''\\<preceq>C T' \\<and> wf_mhead G sig rT' \\<and> wf_mb G T' (sig,rT',b)"; 
by( datac widen_methd 2 1);
by( Clarify_tac 1);
by( ftac subcls_is_class2 1);
by (rewtac is_class_def);
by (Asm_simp_tac 1);
by( dtac method_wf_mdecl 1);
by( rewtac wf_mdecl_def);
by( rewtac is_class_def);
by Auto_tac;
qed "Call_lemma";

Goal "wf_prog wf_mb G ==> method (G,Object) sig = None";
by (Asm_simp_tac 1);
qed "method_Object";
Addsimps [method_Object];

Goalw [max_spec_def] 
  "x \\<in> max_spec G C sig ==> x \\<in> appl_methds G C sig";
by (Fast_tac 1);
qed"max_spec2appl_meths";

Goalw [appl_methds_def] 
"((md,rT),pTs')\\<in>appl_methds G C (mn, pTs) ==> \
\ \\<exists>D b. md = Class D \\<and> method (G,C) (mn, pTs') = Some (D,rT,b) \
\ \\<and> list_all2 (\\<lambda>T T'. G\\<turnstile>T\\<preceq>T') pTs pTs'";
by (Fast_tac 1);
qed "appl_methsD";

bind_thm ("max_spec2mheads", insertI1 RSN (2,(equalityD2 RS subsetD)) RS 
                      max_spec2appl_meths RS appl_methsD);

Goal "(\\<forall>a. v \\<noteq> Addr a) --> (\\<exists>T. typeof t v = Some T \\<and> is_type G T)";
by (rtac val_.induct 1);
by (Fast_tac 5);
by Auto_tac;
qed_spec_mp "is_type_typeof";
Addsimps [is_type_typeof];

Goal "typeof (\\<lambda>a. None) v = Some T \\<longrightarrow> is_type G T";
by (rtac val_.induct 1);
by     Auto_tac;
qed_spec_mp "typeof_empty_is_type";

Goal "wf_prog wf_mb G \\<Longrightarrow> ((G,L)\\<turnstile>e::T \\<longrightarrow> is_type G T) \\<and> \
\      ((G,L)\\<turnstile>es[::]Ts \\<longrightarrow> Ball (set Ts) (is_type G)) \\<and> ((G,L)\\<turnstile>c \\<surd> \\<longrightarrow> True)";
by (rtac ty_expr_ty_exprs_wt_stmt.induct 1);
by Auto_tac;
by (   etac typeof_empty_is_type 1);
by (  asm_full_simp_tac (simpset() addsplits [split_if_asm]) 1);
by ( dtac field_fields 1);
by ( datac fields_is_type 1 1);
by (  Asm_simp_tac 1);
ba 1;
by (auto_tac (claset() addSDs [max_spec2mheads,method_wf_mdecl,is_type_rTI], simpset()addsimps[wf_mdecl_def]));
qed "wt_is_type";

bind_thm ("ty_expr_is_type", permute_prems 0 1 (wt_is_type RS conjunct1 RS mp));
