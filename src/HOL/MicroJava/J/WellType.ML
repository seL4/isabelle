(*  Title:      HOL/MicroJava/J/WellType.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

Goalw [m_head_def]
"\\<lbrakk> m_head G C sig = Some (md,rT); wf_prog wf_mb G; G\\<turnstile>Class T''\\<preceq>Class C\\<rbrakk> \\<Longrightarrow> \
\\\<exists>md' rT' b'. method (G,T'') sig = Some (md',rT',b') \\<and> G\\<turnstile>rT'\\<preceq>rT";
by( forward_tac [widen_Class_RefT] 1);
by( etac exE 1);
by( asm_full_simp_tac (simpset() delsimps [split_paired_Ex]) 1);
by( strip_tac1 1);
by( split_all_tac 1);
by( dtac widen_Class_Class 1);
by( dtac subcls_widen_methd 1);
by   Auto_tac;
qed "widen_methd";


Goal
"\\<lbrakk>m_head G C sig = Some (md,rT); G\\<turnstile>Class T''\\<preceq>Class C; wf_prog wf_mb G\\<rbrakk> \\<Longrightarrow> \
\ \\<exists>T' rT' b. method (G,T'') sig = Some (T',rT',b) \\<and> \
\ G\\<turnstile>rT'\\<preceq>rT \\<and> G\\<turnstile>Class T''\\<preceq>Class T' \\<and> wf_mhead G sig rT' \\<and> wf_mb G T' (sig,rT',b)";
by( datac widen_methd 2 1);
by( Clarsimp_tac 1);
by( dtac method_wf_mdecl 1);
by(  atac 1);
by( rewtac wf_mdecl_def);
by Auto_tac;
qed "Call_lemma";


val m_head_Object = prove_goalw thy [m_head_def]
"\\<And>x. wf_prog wf_mb G \\<Longrightarrow> m_head G Object sig = None" (K [Asm_simp_tac 1]);

Addsimps [m_head_Object];

val max_spec2appl_meths = prove_goalw thy [max_spec_def] 
	"x \\<in> max_spec G C sig \\<longrightarrow> x \\<in> appl_methds G C sig" 
	(fn _ => [Fast_tac 1]) RS mp;

val appl_methsD = prove_goalw thy [appl_methds_def] 
"(mh,pTs')\\<in>appl_methds G C (mn, pTs) \\<longrightarrow> \
\      m_head G C (mn, pTs') = Some mh \\<and> list_all2 (\\<lambda>T T'. G\\<turnstile>T\\<preceq>T') pTs pTs'"
	(K [Fast_tac 1]) RS mp;

val is_type_typeof = prove_goal thy 
	"(\\<forall>a. v \\<noteq> Addr a) \\<longrightarrow> (\\<exists>T. typeof t v = Some T \\<and>  is_type G T)" (K [
	rtac val_.induct 1,
	    Fast_tac 5,
	   ALLGOALS Simp_tac]) RS mp;

Addsimps [is_type_typeof];
