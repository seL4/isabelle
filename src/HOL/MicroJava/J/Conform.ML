(*  Title:      HOL/MicroJava/J/Conform.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

section "hext";

val hextI = prove_goalw thy [hext_def] "\\<And>h. \
\ \\<forall>a C fs . h  a = Some (C,fs) \\<longrightarrow>  \
\     (\\<exists>fs'. h' a = Some (C,fs')) \\<Longrightarrow> h\\<le>|h'" (K [Auto_tac ]);

val hext_objD = prove_goalw thy [hext_def] 
"\\<And>h. \\<lbrakk>h\\<le>|h'; h a = Some (C,fs) \\<rbrakk> \\<Longrightarrow> \\<exists>fs'. h' a = Some (C,fs')" 
	(K [Force_tac 1]);

val hext_refl = prove_goal thy "h\\<le>|h" (K [
	rtac hextI 1,
	Fast_tac 1]);

val hext_new = prove_goal thy "\\<And>h. h a = None \\<Longrightarrow> h\\<le>|h(a\\<mapsto>x)" (K [
	rtac hextI 1,
	safe_tac HOL_cs,
	 ALLGOALS (case_tac "aa = a"),
	   Auto_tac]);

val hext_trans = prove_goal thy "\\<And>h. \\<lbrakk>h\\<le>|h'; h'\\<le>|h''\\<rbrakk> \\<Longrightarrow> h\\<le>|h''" (K [
	rtac hextI 1,
	safe_tac HOL_cs,
	 fast_tac (HOL_cs addDs [hext_objD]) 1]);

Addsimps [hext_refl, hext_new];

val hext_upd_obj = prove_goal thy 
"\\<And>h. h a = Some (C,fs) \\<Longrightarrow> h\\<le>|h(a\\<mapsto>(C,fs'))" (K [
	rtac hextI 1,
	safe_tac HOL_cs,
	 ALLGOALS (case_tac "aa = a"),
	   Auto_tac]);


section "conf";

val conf_Null = prove_goalw thy [conf_def] 
"G,h\\<turnstile>Null\\<Colon>\\<preceq>T = G\\<turnstile>RefT NullT\\<preceq>T" (K [Simp_tac 1]);
Addsimps [conf_Null];

val conf_litval = prove_goalw thy [conf_def] 
"typeof (\\<lambda>v. None) v = Some T \\<longrightarrow> G,h\\<turnstile>v\\<Colon>\\<preceq>T" (K [
	rtac val_.induct 1,
	    Auto_tac]) RS mp;

Goalw [conf_def] "G,s\\<turnstile>Unit\\<Colon>\\<preceq>PrimT Void";
by( Simp_tac 1);
qed "conf_VoidI";

Goalw [conf_def] "G,s\\<turnstile>Bool b\\<Colon>\\<preceq>PrimT Boolean";
by( Simp_tac 1);
qed "conf_BooleanI";

Goalw [conf_def] "G,s\\<turnstile>Intg i\\<Colon>\\<preceq>PrimT Integer";
by( Simp_tac 1);
qed "conf_IntegerI";

Addsimps [conf_VoidI, conf_BooleanI, conf_IntegerI];

val conf_AddrI = prove_goalw thy [conf_def] 
"\\<And>G. \\<lbrakk>h a = Some obj; G\\<turnstile>obj_ty obj\\<preceq>T\\<rbrakk> \\<Longrightarrow> G,h\\<turnstile>Addr a\\<Colon>\\<preceq>T"
(K [Asm_full_simp_tac 1]);

val conf_obj_AddrI = prove_goalw thy [conf_def]
 "\\<And>G. \\<lbrakk>h a = Some (C,fs); G\\<turnstile>C\\<preceq>C D\\<rbrakk> \\<Longrightarrow> G,h\\<turnstile>Addr a\\<Colon>\\<preceq> Class D" 
(K [Asm_full_simp_tac 1]);

Goalw [conf_def] "is_type G T \\<longrightarrow> G,h\\<turnstile>default_val T\\<Colon>\\<preceq>T";
by (res_inst_tac [("y","T")] ty.exhaust 1);
by  (etac ssubst 1);
by  (res_inst_tac [("y","prim_ty")] prim_ty.exhaust 1);
by    (auto_tac (claset(), simpset() addsimps [widen.null]));
qed_spec_mp "defval_conf";

val conf_upd_obj = prove_goalw thy [conf_def] 
"h a = Some (C,fs) \\<longrightarrow> (G,h(a\\<mapsto>(C,fs'))\\<turnstile>x\\<Colon>\\<preceq>T) = (G,h\\<turnstile>x\\<Colon>\\<preceq>T)" (fn _ => [
	rtac impI 1,
	rtac val_.induct 1,
	 ALLGOALS Simp_tac,
	case_tac "loc = a" 1,
	 ALLGOALS Asm_simp_tac]) RS mp;

val conf_widen = prove_goalw thy [conf_def] 
"\\<And>G. wf_prog wf_mb G \\<Longrightarrow> G,h\\<turnstile>x\\<Colon>\\<preceq>T \\<longrightarrow> G\\<turnstile>T\\<preceq>T' \\<longrightarrow> G,h\\<turnstile>x\\<Colon>\\<preceq>T'" (K [
	rtac val_.induct 1,
	    ALLGOALS Simp_tac,
	    ALLGOALS (fast_tac (HOL_cs addIs [widen_trans]))]) RS mp RS mp;

val conf_hext' = prove_goalw thy [conf_def] 
	"\\<And>h. h\\<le>|h' \\<Longrightarrow> (\\<forall>v T. G,h\\<turnstile>v\\<Colon>\\<preceq>T \\<longrightarrow> G,h'\\<turnstile>v\\<Colon>\\<preceq>T)" (K [
	REPEAT (rtac allI 1),
	rtac val_.induct 1,
	 ALLGOALS Simp_tac,
	safe_tac (HOL_cs addSDs [option_map_SomeD]),
	rewtac option_map_def,
	  dtac hext_objD 1,
	   Auto_tac]);
val conf_hext = conf_hext' RS spec RS spec RS mp;

val new_locD = prove_goalw thy [conf_def] 
	"\\<lbrakk>h a = None; G,h\\<turnstile>Addr t\\<Colon>\\<preceq>T\\<rbrakk> \\<Longrightarrow> t\\<noteq>a" (fn prems => [
	cut_facts_tac prems 1,
	Full_simp_tac 1,
	safe_tac HOL_cs,
	Asm_full_simp_tac 1]);

Goalw [conf_def]
 "G,h\\<turnstile>a'\\<Colon>\\<preceq>RefT T \\<longrightarrow> a' = Null |  \
\ (\\<exists>a obj T'. a' = Addr a \\<and>  h a = Some obj \\<and>  obj_ty obj = T' \\<and>  G\\<turnstile>T'\\<preceq>RefT T)";
by(induct_tac "a'" 1);
by(Auto_tac);
qed_spec_mp "conf_RefTD";

val conf_NullTD = prove_goal thy "\\<And>G. G,h\\<turnstile>a'\\<Colon>\\<preceq>RefT NullT \\<Longrightarrow> a' = Null" (K [
	dtac conf_RefTD 1,
	Step_tac 1,
	 Auto_tac]);

val non_npD = prove_goal thy "\\<And>G. \\<lbrakk>a' \\<noteq> Null; G,h\\<turnstile>a'\\<Colon>\\<preceq>RefT t\\<rbrakk> \\<Longrightarrow> \
\ \\<exists>a C fs. a' = Addr a \\<and>  h a = Some (C,fs) \\<and>  G\\<turnstile>Class C\\<preceq>RefT t" (K [
	dtac conf_RefTD 1,
	Step_tac 1,
	 Auto_tac]);

val non_np_objD = prove_goal thy "\\<And>G. \\<lbrakk>a' \\<noteq> Null; G,h\\<turnstile>a'\\<Colon>\\<preceq> Class C; C \\<noteq> Object\\<rbrakk> \\<Longrightarrow> \
\ (\\<exists>a C' fs. a' = Addr a \\<and>  h a = Some (C',fs) \\<and>  G\\<turnstile>C'\\<preceq>C C)" 
	(K[fast_tac (claset() addDs [non_npD]) 1]);

Goal "a' \\<noteq> Null \\<longrightarrow> wf_prog wf_mb G \\<longrightarrow> G,h\\<turnstile>a'\\<Colon>\\<preceq>RefT t \\<longrightarrow>\
\ (\\<forall>C. t = ClassT C \\<longrightarrow> C \\<noteq> Object) \\<longrightarrow> \
\ (\\<exists>a C fs. a' = Addr a \\<and>  h a = Some (C,fs) \\<and>  G\\<turnstile>Class C\\<preceq>RefT t)";
by(rtac impI 1);
by(rtac impI 1);
by(res_inst_tac [("y","t")] ref_ty.exhaust 1);
 by(Safe_tac);
 by(dtac conf_NullTD 1);
 by(contr_tac 1);
by(dtac non_np_objD 1);
  by(atac 1);
 by(Fast_tac 1);
by(Fast_tac 1);
qed_spec_mp "non_np_objD'";

Goal "wf_prog wf_mb G \\<Longrightarrow> \\<forall>Ts Ts'. list_all2 (conf G h) vs Ts \\<longrightarrow> list_all2 (\\<lambda>T T'. G\\<turnstile>T\\<preceq>T') Ts Ts' \\<longrightarrow>  list_all2 (conf G h) vs Ts'";
by(induct_tac "vs" 1);
 by(ALLGOALS Clarsimp_tac);
by(forward_tac [list_all2_lengthD RS sym] 1);
by(full_simp_tac (simpset()addsimps[length_Suc_conv]) 1);
by(Safe_tac);
by(forward_tac [list_all2_lengthD RS sym] 1);
by(full_simp_tac (simpset()addsimps[length_Suc_conv]) 1);
by(Clarify_tac 1);
by(fast_tac (claset() addEs [conf_widen]) 1);
qed_spec_mp "conf_list_gext_widen";


section "lconf";

val lconfD = prove_goalw thy [lconf_def] 
   "\\<And>X. \\<lbrakk> G,h\\<turnstile>vs[\\<Colon>\\<preceq>]Ts; Ts n = Some T \\<rbrakk> \\<Longrightarrow> G,h\\<turnstile>(the (vs n))\\<Colon>\\<preceq>T"
 (K [Force_tac 1]);

val lconf_hext = prove_goalw thy [lconf_def] 
	"\\<And>X. \\<lbrakk> G,h\\<turnstile>l[\\<Colon>\\<preceq>]L; h\\<le>|h' \\<rbrakk> \\<Longrightarrow> G,h'\\<turnstile>l[\\<Colon>\\<preceq>]L" (K [
		fast_tac (claset() addEs [conf_hext]) 1]);
AddEs [lconf_hext];

Goalw [lconf_def] "\\<And>X. \\<lbrakk> G,h\\<turnstile>l[\\<Colon>\\<preceq>]lT; \
\ G,h\\<turnstile>v\\<Colon>\\<preceq>T; lT va = Some T \\<rbrakk> \\<Longrightarrow> G,h\\<turnstile>l(va\\<mapsto>v)[\\<Colon>\\<preceq>]lT";
by( Clarify_tac 1);
by( case_tac "n = va" 1);
 by Auto_tac;
qed "lconf_upd";

Goal "\\<forall>x. P x \\<longrightarrow> R (dv x) x \\<Longrightarrow> (\\<forall>x. map_of fs f = Some x \\<longrightarrow> P x) \\<longrightarrow> \
\ (\\<forall>T. map_of fs f = Some T \\<longrightarrow> \
\ (\\<exists>v. map_of (map (\\<lambda>(f,ft). (f, dv ft)) fs) f = Some v \\<and>  R v T))";
by( induct_tac "fs" 1);
by Auto_tac;
qed_spec_mp "lconf_init_vars_lemma";

Goalw [lconf_def, init_vars_def] 
"\\<forall>n. \\<forall>T. map_of fs n = Some T \\<longrightarrow> is_type G T \\<Longrightarrow> G,h\\<turnstile>init_vars fs[\\<Colon>\\<preceq>]map_of fs";
by Auto_tac;
by( rtac lconf_init_vars_lemma 1);
by(   atac 3);
by(  strip_tac 1);
by(  etac defval_conf 1);
by Auto_tac;
qed "lconf_init_vars";
AddSIs [lconf_init_vars];

val lconf_ext = prove_goalw thy [lconf_def] 
"\\<And>X. \\<lbrakk>G,s\\<turnstile>l[\\<Colon>\\<preceq>]L; G,s\\<turnstile>v\\<Colon>\\<preceq>T\\<rbrakk> \\<Longrightarrow> G,s\\<turnstile>l(vn\\<mapsto>v)[\\<Colon>\\<preceq>]L(vn\\<mapsto>T)" 
	(K [Auto_tac]);

Goalw [lconf_def] "G,h\\<turnstile>l[\\<Colon>\\<preceq>]L \\<Longrightarrow> \\<forall>vs Ts. nodups vns \\<longrightarrow> length Ts = length vns \\<longrightarrow> list_all2 (\\<lambda>v T. G,h\\<turnstile>v\\<Colon>\\<preceq>T) vs Ts \\<longrightarrow> G,h\\<turnstile>l(vns[\\<mapsto>]vs)[\\<Colon>\\<preceq>]L(vns[\\<mapsto>]Ts)";
by( induct_tac "vns" 1);
by(  ALLGOALS Clarsimp_tac);
by( forward_tac [list_all2_lengthD] 1);
by( auto_tac (claset(), simpset() addsimps [length_Suc_conv]));
qed_spec_mp "lconf_ext_list";


section "oconf";

val oconf_hext = prove_goalw thy [oconf_def] 
"\\<And>X. G,h\\<turnstile>obj\\<surd> \\<Longrightarrow> h\\<le>|h' \\<Longrightarrow> G,h'\\<turnstile>obj\\<surd>" (K [Fast_tac 1]);

val oconf_obj = prove_goalw thy [oconf_def,lconf_def] "G,h\\<turnstile>(C,fs)\\<surd> = \
\ (\\<forall>T f. map_of(fields (G,C)) f = Some T \\<longrightarrow> (\\<exists>v. fs f = Some v \\<and>  G,h\\<turnstile>v\\<Colon>\\<preceq>T))"(K [
	Auto_tac]);

val oconf_objD = oconf_obj RS iffD1 RS spec RS spec RS mp;


section "hconf";

Goalw [hconf_def] "\\<lbrakk>G\\<turnstile>h h\\<surd>; h a = Some obj\\<rbrakk> \\<Longrightarrow> G,h\\<turnstile>obj\\<surd>";
by (Fast_tac 1);
qed "hconfD";

Goalw [hconf_def] "\\<forall>a obj. h a=Some obj \\<longrightarrow> G,h\\<turnstile>obj\\<surd> \\<Longrightarrow> G\\<turnstile>h h\\<surd>";
by (Fast_tac 1);
qed "hconfI";


section "conforms";

val conforms_heapD = prove_goalw thy [conforms_def]
	"(h, l)\\<Colon>\\<preceq>(G, lT) \\<Longrightarrow> G\\<turnstile>h h\\<surd>"
	(fn prems => [cut_facts_tac prems 1, Asm_full_simp_tac 1]);

val conforms_localD = prove_goalw thy [conforms_def]
	 "(h, l)\\<Colon>\\<preceq>(G, lT) \\<Longrightarrow> G,h\\<turnstile>l[\\<Colon>\\<preceq>]lT" (fn prems => [
	cut_facts_tac prems 1, Asm_full_simp_tac 1]);

val conformsI = prove_goalw thy [conforms_def] 
"\\<lbrakk>G\\<turnstile>h h\\<surd>; G,h\\<turnstile>l[\\<Colon>\\<preceq>]lT\\<rbrakk> \\<Longrightarrow> (h, l)\\<Colon>\\<preceq>(G, lT)" (fn prems => [
	cut_facts_tac prems 1,
	Simp_tac 1,
	Auto_tac]);

Goal "\\<lbrakk>(h,l)\\<Colon>\\<preceq>(G,lT); h\\<le>|h'; G\\<turnstile>h h'\\<surd> \\<rbrakk> \\<Longrightarrow> (h',l)\\<Colon>\\<preceq>(G,lT)";
by( fast_tac (HOL_cs addDs [conforms_localD] 
  addSEs [conformsI, lconf_hext]) 1);
qed "conforms_hext";

Goal "\\<lbrakk>(h,l)\\<Colon>\\<preceq>(G, lT); G,h(a\\<mapsto>obj)\\<turnstile>obj\\<surd>; h\\<le>|h(a\\<mapsto>obj)\\<rbrakk> \\<Longrightarrow> (h(a\\<mapsto>obj),l)\\<Colon>\\<preceq>(G, lT)";
by( rtac conforms_hext 1);
by   Auto_tac;
by( rtac hconfI 1);
by( dtac conforms_heapD 1);
by( (auto_tac (HOL_cs addEs [oconf_hext] addDs [hconfD],
		simpset()delsimps[split_paired_All])));
qed "conforms_upd_obj";

Goalw [conforms_def] 
"\\<lbrakk>(h, l)\\<Colon>\\<preceq>(G, lT); G,h\\<turnstile>v\\<Colon>\\<preceq>T; lT va = Some T\\<rbrakk> \\<Longrightarrow> \
\ (h, l(va\\<mapsto>v))\\<Colon>\\<preceq>(G, lT)";
by( auto_tac (claset() addEs [lconf_upd], simpset()));
qed "conforms_upd_local";
