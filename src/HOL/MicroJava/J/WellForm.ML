(*  Title:      HOL/MicroJava/J/WellForm.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

val class_wf = prove_goalw thy [wf_prog_def, Let_def, class_def]
 "\\<And>X. \\<lbrakk>class G C = Some c; wf_prog wtm G\\<rbrakk> \\<Longrightarrow> wf_cdecl wtm G (C,c)" (K [
	Asm_full_simp_tac 1,
	fast_tac (set_cs addDs [get_in_set]) 1]);

val class_Object = prove_goalw thy [wf_prog_def, Let_def, ObjectC_def,class_def]
	"\\<And>X. wf_prog wtm G \\<Longrightarrow> class G Object = Some (None, [], [])" (K [
	safe_tac set_cs,
	dtac in_set_get 1,
	 Auto_tac]);
Addsimps [class_Object];

val is_class_Object = prove_goalw thy [is_class_def] 
	"\\<And>X. wf_prog wtm G \\<Longrightarrow> is_class G Object" (K [Asm_simp_tac 1]);
Addsimps [is_class_Object];

Goal "\\<lbrakk>G\\<turnstile>C\\<prec>C1D; wf_prog wtm G\\<rbrakk> \\<Longrightarrow> D \\<noteq> C \\<and> \\<not>  G\\<turnstile>D\\<prec>C C";
by( forward_tac [r_into_trancl] 1);
by( dtac subcls1D 1);
by( strip_tac1 1);
by( dtac class_wf 1);
by(  atac 1);
by( rewtac wf_cdecl_def);
by( Clarsimp_tac 1);
qed "subcls1_wfD";

val wf_cdecl_supD = prove_goalw thy [wf_cdecl_def] 
"\\<And>X. \\<lbrakk>wf_cdecl wtm G (C, sc, r); C \\<noteq> Object\\<rbrakk> \\<Longrightarrow> \\<exists>D. sc = Some D \\<and> is_class G D" (K [
	pair_tac "r" 1,
	Asm_full_simp_tac 1,
	strip_tac1 1,
	option_case_tac 1,
	Fast_tac 1]);

local
val lemma = prove_goal thy "\\<And>X. \\<lbrakk>wf_prog wtm G; G\\<turnstile>C\\<prec>C D\\<rbrakk> \\<Longrightarrow> C=Object \\<longrightarrow> R" (K [
	etac trancl_trans_induct 1,
	 atac 2,
	rewtac subcls1_def,
	Auto_tac]);
in
val subcls_Object = prove_goal thy "\\<And>X. \\<lbrakk>wf_prog wtm G; G\\<turnstile>Object\\<prec>C C\\<rbrakk> \\<Longrightarrow> R" (K [
	etac (lemma RS mp) 1,
	Auto_tac]);
end;

Goal "\\<lbrakk>wf_prog wt G; G\\<turnstile>C\\<prec>C D\\<rbrakk> \\<Longrightarrow> \\<not>  G\\<turnstile>D\\<prec>C C";
by(etac tranclE 1);
by(ALLGOALS(fast_tac (HOL_cs addSDs [subcls1_wfD] addIs [trancl_trans])));
qed "subcls_asym";

val subcls_irrefl = prove_goal thy "\\<And>X. \\<lbrakk>wf_prog wtm G; G\\<turnstile>C\\<prec>C D\\<rbrakk> \\<Longrightarrow> C \\<noteq> D" (K [
	etac trancl_trans_induct 1,
	 fast_tac (HOL_cs addDs [subcls1_wfD]) 1,
	fast_tac (HOL_cs addDs [subcls_asym]) 1]);

val acyclic_subcls1 = prove_goalw thy [acyclic_def] 
	"\\<And>X. wf_prog wt G \\<Longrightarrow> acyclic (subcls1 G)" (K [
	strip_tac1 1,
	fast_tac (HOL_cs addDs [subcls_irrefl]) 1]);

val wf_subcls1 = prove_goal thy "\\<And>X. wf_prog wtm G \\<Longrightarrow> wf ((subcls1 G)^-1)" (K [
	rtac finite_acyclic_wf 1,
	 stac finite_converse 1,
	 rtac finite_subcls1 1,
	stac acyclic_converse 1,
	etac acyclic_subcls1 1]);


val major::prems = goal thy
  "\\<lbrakk>wf_prog wt G; \\<And>C. \\<forall>D. G\\<turnstile>C\\<prec>C D \\<longrightarrow> P D \\<Longrightarrow> P C\\<rbrakk> \\<Longrightarrow> P C";
by(cut_facts_tac [major RS wf_subcls1] 1);
by(dtac wf_trancl 1);
by(asm_full_simp_tac (HOL_ss addsimps [trancl_converse]) 1);
by(eres_inst_tac [("a","C")] wf_induct 1);
by(resolve_tac prems 1);
by(Auto_tac);
qed "subcls_induct";

val prems = goal thy "\\<lbrakk>is_class G C; wf_prog wtm G; P Object; \
\\\<And>C D fs ms. \\<lbrakk>C \\<noteq> Object; is_class G C; class G C = Some (Some D,fs,ms) \\<and> \
\   wf_cdecl wtm G (C, Some D,fs,ms) \\<and> G\\<turnstile>C\\<prec>C1D \\<and> is_class G D \\<and> P D\\<rbrakk> \\<Longrightarrow> P C\
\ \\<rbrakk> \\<Longrightarrow> P C";
by( cut_facts_tac prems 1);
by( rtac impE 1);
by(   atac 2);
by(  atac 2);
by( etac thin_rl 1);
by( rtac subcls_induct 1);
by(  atac 1);
by( rtac impI 1);
by( case_tac "C = Object" 1);
by(  Fast_tac 1);
by( ex_ftac is_classD 1);
by( forward_tac [class_wf] 1);
by(  atac 1);
by( forward_tac [wf_cdecl_supD] 1);
by(  atac 1);
by( strip_tac1 1);
by( rtac (hd (tl (tl (tl prems)))) 1);
by(   atac 1);
by(  atac 1);
by( subgoal_tac "G\\<turnstile>C\\<prec>C1D" 1);
by(  fast_tac (HOL_cs addIs [r_into_trancl]) 1);
by( etac subcls1I 1);
qed "subcls1_induct";

Goal "wf_prog wtm G \\<Longrightarrow> method (G,C) = \
\ (case class G C of None \\<Rightarrow> empty | Some (sc,fs,ms) \\<Rightarrow> \
\ (case sc of None \\<Rightarrow> empty | Some D \\<Rightarrow> method (G,D)) \\<oplus> \
\ map_of (map (\\<lambda>(s,m). (s,(C,m))) ms))";
by( stac (method_TC RS (wf_subcls1_rel RS (hd method.rules))) 1);
by( clarsimp_tac (claset(), simpset() addsimps [wf_subcls1,empty_def] 
		addsplits [option.split]) 1);
by( case_tac "C = Object" 1);
by(  Asm_full_simp_tac 1);
by( dtac class_wf 1);
by(  atac 1);
by( dtac wf_cdecl_supD 1);
by(  atac 1);
by( Asm_full_simp_tac 1);
val method_rec = result();

Goal "\\<lbrakk>class G C = Some (sc,fs,ms); wf_prog wtm G\\<rbrakk> \\<Longrightarrow> fields (G,C) = \
\ map (\\<lambda>(fn,ft). ((fn,C),ft)) fs @ \
\ (case sc of None \\<Rightarrow> [] | Some D \\<Rightarrow> fields (G,D))";
by( stac (fields_TC RS (wf_subcls1_rel RS (hd fields.rules))) 1);
by( asm_simp_tac (simpset() addsimps [wf_subcls1,empty_def]) 1);
by( option_case_tac2 "sc" 1);
by(  Asm_simp_tac 1);
by( case_tac "C = Object" 1);
by(  rotate_tac 2 1);
by(  Asm_full_simp_tac 1);
by( dtac class_wf 1);
by(  atac 1);
by( dtac wf_cdecl_supD 1);
by(  atac 1);
by( Asm_full_simp_tac 1);
val fields_rec = result();

val method_Object = prove_goal thy "\\<And>X. wf_prog wtm G \\<Longrightarrow> method (G,Object) = empty"
	(K [stac method_rec 1,Auto_tac]);
val fields_Object = prove_goal thy "\\<And>X. wf_prog wtm G \\<Longrightarrow> fields (G,Object) = []"(K [
	stac fields_rec 1,Auto_tac]);
Addsimps [method_Object, fields_Object];
val field_Object = prove_goalw thy [field_def]
 "\\<And>X. wf_prog wtm G \\<Longrightarrow> field (G,Object) = empty" (K [Asm_simp_tac 1]);
Addsimps [field_Object];

val subcls_C_Object = prove_goal thy 
	"\\<And>X. \\<lbrakk>is_class G C; wf_prog wtm G \\<rbrakk> \\<Longrightarrow> C \\<noteq> Object \\<longrightarrow> G\\<turnstile>C\\<prec>C Object" (K [
	etac subcls1_induct 1,
	  atac 1,
	 Fast_tac 1,
	safe_tac (HOL_cs addSDs [wf_cdecl_supD] addss (simpset())),
	 fast_tac (HOL_cs addIs [r_into_trancl]) 1,
	rtac trancl_trans 1,
	 atac 2,
	rtac r_into_trancl 1,
	rtac subcls1I 1,
	ALLGOALS Asm_simp_tac]) RS mp;

val is_type_rTI = prove_goalw thy [wf_mhead_def]
	"\\<And>sig. wf_mhead G sig rT \\<Longrightarrow> is_type G rT"
	(K [split_all_tac 1, Auto_tac]);

val widen_Class_Object = prove_goal thy 
	"\\<lbrakk>wf_prog wtm G; is_class G C\\<rbrakk> \\<Longrightarrow> G\\<turnstile>Class C\\<preceq>Class Object" (fn prems => [
	cut_facts_tac prems 1,
	case_tac "C=Object" 1,
	 hyp_subst_tac 1,
	 Asm_simp_tac 1,
	rtac widen.subcls 1,
	fast_tac (HOL_cs addEs [subcls_C_Object]) 1]);

val widen_trans = prove_goal thy "\\<lbrakk>wf_prog wtm G; G\\<turnstile>S\\<preceq>U; G\\<turnstile>U\\<preceq>T\\<rbrakk> \\<Longrightarrow> G\\<turnstile>S\\<preceq>T"
(fn prems=> [cut_facts_tac prems 1, 
	fast_tac (HOL_cs addEs [widen_trans_lemma, widen_Class_Object, 
				subcls_Object]) 1]);

val fields_mono = prove_goal thy 
"\\<And>X. \\<lbrakk>G\\<turnstile>C'\\<prec>C C; wf_prog wtm G\\<rbrakk> \\<Longrightarrow> \
\ x \\<in> set (fields (G,C)) \\<longrightarrow> x \\<in> set (fields (G,C'))" (K [
	etac trancl_trans_induct 1,
	 safe_tac (HOL_cs addSDs [subcls1D]),
	stac fields_rec 1,
	  Auto_tac]) RS mp;

Goal "\\<lbrakk>is_class G C; wf_prog wtm G\\<rbrakk> \\<Longrightarrow> \
\ \\<forall>((fn,fd),fT)\\<in>set (fields (G,C)). G\\<turnstile>Class C\\<preceq>Class fd";
by( etac subcls1_induct 1);
by(   atac 1);
by(  Asm_simp_tac 1);
by( safe_tac HOL_cs);
by( stac fields_rec 1);
by(   atac 1);
by(  atac 1);
by( Simp_tac 1);
by( rtac ballI 1);
by( split_all_tac 1);
by( Simp_tac 1);
by( etac UnE 1);
by(  dtac split_Pair_eq 1);
by(  SELECT_GOAL (Auto_tac) 1);
by( rtac widen_trans 1);
by(   atac 1);
by(  etac (r_into_trancl RS widen.subcls) 1);
by( etac BallE 1);
by(  contr_tac 1);
by( Asm_full_simp_tac 1);
val widen_fields_defpl' = result();

Goal "\\<lbrakk>is_class G C; wf_prog wtm G; ((fn,fd),fT) \\<in> set (fields (G,C))\\<rbrakk> \\<Longrightarrow> \
\ G\\<turnstile>Class C\\<preceq>Class fd";
by( dtac widen_fields_defpl' 1);
by(  atac 1);
(*###################*)
by( dtac bspec 1);
auto();
val widen_fields_defpl = result();


Goal "\\<lbrakk>is_class G C; wf_prog wtm G\\<rbrakk> \\<Longrightarrow> unique (fields (G,C))";
by( etac subcls1_induct 1);
by(   atac 1);
by(  safe_tac (HOL_cs addSDs [wf_cdecl_supD]));
by(  Asm_simp_tac 1);
by( dtac subcls1_wfD 1);
by(  atac 1);
by( stac fields_rec 1);
by   Auto_tac;
by( rotate_tac ~1 1);
by( ex_ftac is_classD 1);
by( forward_tac [class_wf] 1);
by  Auto_tac;
by( asm_full_simp_tac (simpset() addsimps [wf_cdecl_def]) 1);
by( etac unique_append 1);
by(  rtac unique_map_Pair 1);
by(  Step_tac 1);
by (EVERY1[dtac widen_fields_defpl, atac, atac]);
by( Asm_full_simp_tac 1);
by( dtac split_Pair_eq 1);
by( fast_tac (HOL_cs addSDs [widen_Class_Class]) 1);
val unique_fields = result();

Goal
"\\<lbrakk>wf_prog wtm G; G\\<turnstile>Class C'\\<preceq>Class C; map_of(fields (G,C )) f = Some ft\\<rbrakk> \\<Longrightarrow> \
\                          map_of (fields (G,C')) f = Some ft";
by( dtac widen_Class_Class 1);
by( etac disjE 1);
by(  Asm_simp_tac 1);
by( rtac table_mono 1);
by(   atac 3);
by(  rtac unique_fields 1);
by(   etac subcls_is_class 1);
by(  atac 1);
by( fast_tac (HOL_cs addEs [fields_mono]) 1);
val widen_fields_mono = result();


val cfs_fields_lemma = prove_goalw thy [field_def] 
"\\<And>X. field (G,C) fn = Some (fd, fT) \\<Longrightarrow> map_of(fields (G,C)) (fn, fd) = Some fT"
(K [rtac table_map_Some 1, Asm_full_simp_tac 1]);

val widen_cfs_fields = prove_goal thy "\\<And>X. \\<lbrakk>field (G,C) fn = Some (fd, fT);\
\  G\\<turnstile>Class C'\\<preceq>Class C; wf_prog wtm G\\<rbrakk> \\<Longrightarrow> map_of (fields (G,C')) (fn, fd) = Some fT" (K[
fast_tac (HOL_cs addIs [widen_fields_mono, cfs_fields_lemma]) 1]);

Goal "wf_prog wtm G \\<Longrightarrow> method (G,C) sig = Some (md,mh,m)\
\  \\<longrightarrow> G\\<turnstile>Class C\\<preceq>Class md \\<and> wf_mdecl wtm G md (sig,(mh,m))";
by( case_tac "is_class G C" 1);
by(  forw_inst_tac [("C","C")] method_rec 2);
by(    asm_full_simp_tac (simpset() addsimps [is_class_def] 
	delsimps [not_None_eq]) 2);
by( etac subcls1_induct 1);
by(   atac 1);
by(  Force_tac 1);
by( forw_inst_tac [("C","C")] method_rec 1);
by( strip_tac1 1);
by( rotate_tac ~1 1);
by( Asm_full_simp_tac 1);
by( dtac override_SomeD 1);
by( etac disjE 1);
by(  thin_tac "?P \\<longrightarrow> ?Q" 1);
by(  Clarify_tac 2);
by(  rtac widen_trans 2);
by(    atac 2);
by(   atac 3);
by(  rtac widen.subcls 2);
by(  rtac r_into_trancl 2);
by(  fast_tac (HOL_cs addIs [subcls1I]) 2);
by( forward_tac [table_mapf_SomeD] 1);
by( strip_tac1 1);
by( Asm_full_simp_tac 1);
by( rewtac wf_cdecl_def);
by( Asm_full_simp_tac 1);
val method_wf_mdecl = result() RS mp;

Goal "\\<lbrakk>G\\<turnstile>T\\<prec>C T'; wf_prog wt G\\<rbrakk> \\<Longrightarrow> \
\  \\<forall>D rT b. method (G,T') sig = Some (D,rT ,b) \\<longrightarrow>\
\ (\\<exists>D' rT' b'. method (G,T) sig = Some (D',rT',b') \\<and> G\\<turnstile>rT'\\<preceq>rT)";
by( etac trancl_trans_induct 1);
by(  strip_tac1 2);
by(  EVERY[dtac spec 2, dtac spec 2, dtac spec 2, mp_tac 2]);
by(  fast_tac (HOL_cs addEs [widen_trans]) 2);
by( strip_tac1 1);
by( dtac subcls1D 1);
by( strip_tac1 1);
by( stac method_rec 1);
by(  atac 1);
by( rewtac override_def);
by( asm_simp_tac (simpset() delsimps [split_paired_Ex]) 1);
by( case_tac "\\<exists>z. map_of(map (\\<lambda>(s,m). (s, ?C, m)) ms) sig = Some z" 1);
by(  etac exE 1);
by(  asm_full_simp_tac (HOL_ss addsimps [not_None_eq RS sym]) 2);
by(  ALLGOALS (rotate_tac ~1 THEN' forward_tac[ssubst] THEN' (fn n=>atac(n+1))));
by(  ALLGOALS (asm_simp_tac (simpset() delsimps [split_paired_Ex])));
by( dtac class_wf 1);
by(  atac 1);
by( split_all_tac 1);
by( rewtac wf_cdecl_def);
by( dtac table_mapf_Some2 1);
by( Clarsimp_tac 1);
by( dres_inst_tac [("xys1","ms")] get_in_set 1);
by Auto_tac;
qed_spec_mp "subcls_widen_methd";


Goal
 "\\<lbrakk> G\\<turnstile>Class C\\<preceq>Class D; wf_prog wt G; \
\    method (G,D) sig = Some (md, rT, b) \\<rbrakk> \
\ \\<Longrightarrow> \\<exists>mD' rT' b'. method (G,C) sig= Some(mD',rT',b') \\<and> G\\<turnstile>rT'\\<preceq>rT";
by(auto_tac (claset() addSDs [widen_Class_Class]
                      addDs [subcls_widen_methd,method_wf_mdecl],
             simpset() addsimps [wf_mdecl_def,wf_mhead_def,split_def]));
qed "subtype_widen_methd";


Goal "wf_prog wt G \\<Longrightarrow> \\<forall>D. method (G,C) sig = Some(D,mh,code) \\<longrightarrow> is_class G D \\<and> method (G,D) sig = Some(D,mh,code)";
by( case_tac "is_class G C" 1);
by(  forw_inst_tac [("C","C")] method_rec 2);
by(    asm_full_simp_tac (simpset() addsimps [is_class_def] 
	delsimps [not_None_eq]) 2);
by (etac subcls1_induct 1);
  ba 1;
 by (Asm_full_simp_tac 1);
by (stac method_rec 1);
 ba 1;
by (Clarify_tac 1);
by (eres_inst_tac [("x","Da")] allE 1);
by (Clarsimp_tac 1);
 by (asm_full_simp_tac (simpset() addsimps [map_of_map]) 1);
 by (Clarify_tac 1);
 by (stac method_rec 1);
  ba 1;
 by (asm_full_simp_tac (simpset() addsimps [override_def,map_of_map] addsplits [option.split]) 1);
qed_spec_mp "method_in_md";

writeln"OK";

Goal "\\<lbrakk>is_class G C; wf_prog wtm G\\<rbrakk> \\<Longrightarrow> \
\ \\<forall>f\\<in>set (fields (G,C)). is_type G (snd f)";
by( etac subcls1_induct 1);
by(   atac 1);
by(  Asm_simp_tac 1);
by( strip_tac1 1);
by( stac fields_rec 1);
by(   atac 1);
by(  atac 1);
by( Asm_simp_tac 1);
by( safe_tac set_cs);
by(  Fast_tac 2);
by( dtac class_wf 1);
by(  atac 1);
by( rewtac wf_cdecl_def);
by( Asm_full_simp_tac 1);
by( strip_tac1 1);
by( EVERY[dtac bspec 1, atac 1]);
by( rewtac wf_fdecl_def);
by( split_all_tac 1);
by( Asm_full_simp_tac 1);
val is_type_fields = result() RS bspec;
