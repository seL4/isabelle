(*  Title:      HOL/MicroJava/J/WellType.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

Goal
"\\<lbrakk> method (G,C) sig = Some (md,rT,b); wf_prog wf_mb G; G\\<turnstile>T''\\<preceq>C C\\<rbrakk>\
\ \\<Longrightarrow> \\<exists>md' rT' b'. method (G,T'') sig = Some (md',rT',b') \\<and> G\\<turnstile>rT'\\<preceq>rT";
by( dtac subcls_widen_methd 1);
by   Auto_tac;
qed "widen_methd";


Goal
"\\<lbrakk>method (G,C) sig = Some (md,rT,b); G\\<turnstile>T''\\<preceq>C C; wf_prog wf_mb G\\<rbrakk> \\<Longrightarrow> \
\ \\<exists>T' rT' b. method (G,T'') sig = Some (T',rT',b) \\<and> \
\ G\\<turnstile>rT'\\<preceq>rT \\<and> G\\<turnstile>T''\\<preceq>C T' \\<and> wf_mhead G sig rT' \\<and> wf_mb G T' (sig,rT',b)";
by( datac widen_methd 2 1);
by( Clarsimp_tac 1);
by( dtac method_wf_mdecl 1);
by(  atac 1);
by( rewtac wf_mdecl_def);
by Auto_tac;
qed "Call_lemma";


Goal "wf_prog wf_mb G \\<Longrightarrow> method (G,Object) sig = None";
by (Asm_simp_tac 1);
qed "method_Object";
Addsimps [method_Object];

Goalw [max_spec_def] 
  "x \\<in> max_spec G C sig \\<Longrightarrow> x \\<in> appl_methds G C sig";
by (Fast_tac 1);
qed"max_spec2appl_meths";

Goalw [appl_methds_def] 
"((md,rT),pTs')\\<in>appl_methds G C (mn, pTs) \\<Longrightarrow> \
\ \\<exists>D b. md = Class D \\<and> method (G,C) (mn, pTs') = Some (D,rT,b) \
\ \\<and> list_all2 (\\<lambda>T T'. G\\<turnstile>T\\<preceq>T') pTs pTs'";
by (Fast_tac 1);
qed "appl_methsD";

val is_type_typeof = prove_goal thy 
	"(\\<forall>a. v \\<noteq> Addr a) \\<longrightarrow> (\\<exists>T. typeof t v = Some T \\<and>  is_type G T)" (K [
	rtac val_.induct 1,
	    Fast_tac 5,
	   ALLGOALS Simp_tac]) RS mp;
Addsimps [is_type_typeof];
