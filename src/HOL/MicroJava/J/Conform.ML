(*  Title:      HOL/MicroJava/J/Conform.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

section "hext";

val hextI = prove_goalw thy [hext_def] "!!h. \
\ \\<forall>a C fs . h  a = Some (C,fs) -->  \
\     (\\<exists>fs'. h' a = Some (C,fs')) ==> h\\<le>|h'" (K [Auto_tac ]);

val hext_objD = prove_goalw thy [hext_def] 
"!!h. [|h\\<le>|h'; h a = Some (C,fs) |] ==> \\<exists>fs'. h' a = Some (C,fs')" 
	(K [Force_tac 1]);

val hext_refl = prove_goal thy "h\\<le>|h" (K [
	rtac hextI 1,
	Fast_tac 1]);

val hext_new = prove_goal thy "!!h. h a = None ==> h\\<le>|h(a\\<mapsto>x)" (K [
	rtac hextI 1,
	safe_tac HOL_cs,
	 ALLGOALS (case_tac "aa = a"),
	   Auto_tac]);

val hext_trans = prove_goal thy "!!h. [|h\\<le>|h'; h'\\<le>|h''|] ==> h\\<le>|h''" (K [
	rtac hextI 1,
	safe_tac HOL_cs,
	 fast_tac (HOL_cs addDs [hext_objD]) 1]);

Addsimps [hext_refl, hext_new];

val hext_upd_obj = prove_goal thy 
"!!h. h a = Some (C,fs) ==> h\\<le>|h(a\\<mapsto>(C,fs'))" (K [
	rtac hextI 1,
	safe_tac HOL_cs,
	 ALLGOALS (case_tac "aa = a"),
	   Auto_tac]);


section "conf";

val conf_Null = prove_goalw thy [conf_def] 
"G,h\\<turnstile>Null::\\<preceq>T = G\\<turnstile>RefT NullT\\<preceq>T" (K [Simp_tac 1]);
Addsimps [conf_Null];

val conf_litval = prove_goalw thy [conf_def] 
"typeof (\\<lambda>v. None) v = Some T --> G,h\\<turnstile>v::\\<preceq>T" (K [
	rtac val_.induct 1,
	    Auto_tac]) RS mp;

Goalw [conf_def] "G,s\\<turnstile>Unit::\\<preceq>PrimT Void";
by( Simp_tac 1);
qed "conf_VoidI";

Goalw [conf_def] "G,s\\<turnstile>Bool b::\\<preceq>PrimT Boolean";
by( Simp_tac 1);
qed "conf_BooleanI";

Goalw [conf_def] "G,s\\<turnstile>Intg i::\\<preceq>PrimT Integer";
by( Simp_tac 1);
qed "conf_IntegerI";

Addsimps [conf_VoidI, conf_BooleanI, conf_IntegerI];

val conf_AddrI = prove_goalw thy [conf_def] 
"!!G. [|h a = Some obj; G\\<turnstile>obj_ty obj\\<preceq>T|] ==> G,h\\<turnstile>Addr a::\\<preceq>T"
(K [Asm_full_simp_tac 1]);

val conf_obj_AddrI = prove_goalw thy [conf_def]
 "!!G. [|h a = Some (C,fs); G\\<turnstile>C\\<preceq>C D|] ==> G,h\\<turnstile>Addr a::\\<preceq> Class D" 
(K [Asm_full_simp_tac 1]);

Goalw [conf_def] "is_type G T --> G,h\\<turnstile>default_val T::\\<preceq>T";
by (res_inst_tac [("y","T")] ty.exhaust 1);
by  (etac ssubst 1);
by  (res_inst_tac [("y","prim_ty")] prim_ty.exhaust 1);
by    (auto_tac (claset(), simpset() addsimps [widen.null]));
qed_spec_mp "defval_conf";

val conf_upd_obj = prove_goalw thy [conf_def] 
"h a = Some (C,fs) --> (G,h(a\\<mapsto>(C,fs'))\\<turnstile>x::\\<preceq>T) = (G,h\\<turnstile>x::\\<preceq>T)" (fn _ => [
	rtac impI 1,
	rtac val_.induct 1,
	 ALLGOALS Simp_tac,
	case_tac "loc = a" 1,
	 ALLGOALS Asm_simp_tac]) RS mp;

val conf_widen = prove_goalw thy [conf_def] 
"!!G. wf_prog wf_mb G ==> G,h\\<turnstile>x::\\<preceq>T --> G\\<turnstile>T\\<preceq>T' --> G,h\\<turnstile>x::\\<preceq>T'" (K [
	rtac val_.induct 1,
	    ALLGOALS Simp_tac,
	    ALLGOALS (fast_tac (HOL_cs addIs [widen_trans]))]) RS mp RS mp;
bind_thm ("conf_widen", conf_widen);

val conf_hext' = prove_goalw thy [conf_def] 
	"!!h. h\\<le>|h' ==> (\\<forall>v T. G,h\\<turnstile>v::\\<preceq>T --> G,h'\\<turnstile>v::\\<preceq>T)" (K [
	REPEAT (rtac allI 1),
	rtac val_.induct 1,
	 ALLGOALS Simp_tac,
	safe_tac (HOL_cs addSDs [option_map_SomeD]),
	rewtac option_map_def,
	  dtac hext_objD 1,
	   Auto_tac]);
val conf_hext = conf_hext' RS spec RS spec RS mp;
bind_thm ("conf_hext", conf_hext);

val new_locD = prove_goalw thy [conf_def] 
	"[|h a = None; G,h\\<turnstile>Addr t::\\<preceq>T|] ==> t\\<noteq>a" (fn prems => [
	cut_facts_tac prems 1,
	Full_simp_tac 1,
	safe_tac HOL_cs,
	Asm_full_simp_tac 1]);

Goalw [conf_def]
 "G,h\\<turnstile>a'::\\<preceq>RefT T --> a' = Null |  \
\ (\\<exists>a obj T'. a' = Addr a \\<and>  h a = Some obj \\<and>  obj_ty obj = T' \\<and>  G\\<turnstile>T'\\<preceq>RefT T)";
by(induct_tac "a'" 1);
by(Auto_tac);
qed_spec_mp "conf_RefTD";

val conf_NullTD = prove_goal thy "!!G. G,h\\<turnstile>a'::\\<preceq>RefT NullT ==> a' = Null" (K [
	dtac conf_RefTD 1,
	Step_tac 1,
	 Auto_tac]);

val non_npD = prove_goal thy "!!G. [|a' \\<noteq> Null; G,h\\<turnstile>a'::\\<preceq>RefT t|] ==> \
\ \\<exists>a C fs. a' = Addr a \\<and>  h a = Some (C,fs) \\<and>  G\\<turnstile>Class C\\<preceq>RefT t" (K [
	dtac conf_RefTD 1,
	Step_tac 1,
	 Auto_tac]);

val non_np_objD = prove_goal thy "!!G. [|a' \\<noteq> Null; G,h\\<turnstile>a'::\\<preceq> Class C; C \\<noteq> Object|] ==> \
\ (\\<exists>a C' fs. a' = Addr a \\<and>  h a = Some (C',fs) \\<and>  G\\<turnstile>C'\\<preceq>C C)" 
	(K[fast_tac (claset() addDs [non_npD]) 1]);

Goal "a' \\<noteq> Null --> wf_prog wf_mb G --> G,h\\<turnstile>a'::\\<preceq>RefT t -->\
\ (\\<forall>C. t = ClassT C --> C \\<noteq> Object) --> \
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

Goal "wf_prog wf_mb G ==> \\<forall>Ts Ts'. list_all2 (conf G h) vs Ts --> list_all2 (\\<lambda>T T'. G\\<turnstile>T\\<preceq>T') Ts Ts' -->  list_all2 (conf G h) vs Ts'";
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
   "!!X. [| G,h\\<turnstile>vs[::\\<preceq>]Ts; Ts n = Some T |] ==> G,h\\<turnstile>(the (vs n))::\\<preceq>T"
 (K [Force_tac 1]);

val lconf_hext = prove_goalw thy [lconf_def] 
	"!!X. [| G,h\\<turnstile>l[::\\<preceq>]L; h\\<le>|h' |] ==> G,h'\\<turnstile>l[::\\<preceq>]L" (K [
		fast_tac (claset() addEs [conf_hext]) 1]);
AddEs [lconf_hext];

Goalw [lconf_def] "!!X. [| G,h\\<turnstile>l[::\\<preceq>]lT; \
\ G,h\\<turnstile>v::\\<preceq>T; lT va = Some T |] ==> G,h\\<turnstile>l(va\\<mapsto>v)[::\\<preceq>]lT";
by( Clarify_tac 1);
by( case_tac "n = va" 1);
 by Auto_tac;
qed "lconf_upd";

Goal "\\<forall>x. P x --> R (dv x) x ==> (\\<forall>x. map_of fs f = Some x --> P x) --> \
\ (\\<forall>T. map_of fs f = Some T --> \
\ (\\<exists>v. map_of (map (\\<lambda>(f,ft). (f, dv ft)) fs) f = Some v \\<and>  R v T))";
by( induct_tac "fs" 1);
by Auto_tac;
qed_spec_mp "lconf_init_vars_lemma";

Goalw [lconf_def, init_vars_def] 
"\\<forall>n. \\<forall>T. map_of fs n = Some T --> is_type G T ==> G,h\\<turnstile>init_vars fs[::\\<preceq>]map_of fs";
by Auto_tac;
by( rtac lconf_init_vars_lemma 1);
by(   atac 3);
by(  strip_tac 1);
by(  etac defval_conf 1);
by Auto_tac;
qed "lconf_init_vars";
AddSIs [lconf_init_vars];

val lconf_ext = prove_goalw thy [lconf_def] 
"!!X. [|G,s\\<turnstile>l[::\\<preceq>]L; G,s\\<turnstile>v::\\<preceq>T|] ==> G,s\\<turnstile>l(vn\\<mapsto>v)[::\\<preceq>]L(vn\\<mapsto>T)" 
	(K [Auto_tac]);

Goalw [lconf_def] "G,h\\<turnstile>l[::\\<preceq>]L ==> \\<forall>vs Ts. nodups vns --> length Ts = length vns --> list_all2 (\\<lambda>v T. G,h\\<turnstile>v::\\<preceq>T) vs Ts --> G,h\\<turnstile>l(vns[\\<mapsto>]vs)[::\\<preceq>]L(vns[\\<mapsto>]Ts)";
by( induct_tac "vns" 1);
by(  ALLGOALS Clarsimp_tac);
by( forward_tac [list_all2_lengthD] 1);
by( auto_tac (claset(), simpset() addsimps [length_Suc_conv]));
qed_spec_mp "lconf_ext_list";


section "oconf";

val oconf_hext = prove_goalw thy [oconf_def] 
"!!X. G,h\\<turnstile>obj\\<surd> ==> h\\<le>|h' ==> G,h'\\<turnstile>obj\\<surd>" (K [Fast_tac 1]);

val oconf_obj = prove_goalw thy [oconf_def,lconf_def] "G,h\\<turnstile>(C,fs)\\<surd> = \
\ (\\<forall>T f. map_of(fields (G,C)) f = Some T --> (\\<exists>v. fs f = Some v \\<and>  G,h\\<turnstile>v::\\<preceq>T))"(K [
	Auto_tac]);

val oconf_objD = oconf_obj RS iffD1 RS spec RS spec RS mp;


section "hconf";

Goalw [hconf_def] "[|G\\<turnstile>h h\\<surd>; h a = Some obj|] ==> G,h\\<turnstile>obj\\<surd>";
by (Fast_tac 1);
qed "hconfD";

Goalw [hconf_def] "\\<forall>a obj. h a=Some obj --> G,h\\<turnstile>obj\\<surd> ==> G\\<turnstile>h h\\<surd>";
by (Fast_tac 1);
qed "hconfI";


section "conforms";

val conforms_heapD = prove_goalw thy [conforms_def]
	"(h, l)::\\<preceq>(G, lT) ==> G\\<turnstile>h h\\<surd>"
	(fn prems => [cut_facts_tac prems 1, Asm_full_simp_tac 1]);

val conforms_localD = prove_goalw thy [conforms_def]
	 "(h, l)::\\<preceq>(G, lT) ==> G,h\\<turnstile>l[::\\<preceq>]lT" (fn prems => [
	cut_facts_tac prems 1, Asm_full_simp_tac 1]);

val conformsI = prove_goalw thy [conforms_def] 
"[|G\\<turnstile>h h\\<surd>; G,h\\<turnstile>l[::\\<preceq>]lT|] ==> (h, l)::\\<preceq>(G, lT)" (fn prems => [
	cut_facts_tac prems 1,
	Simp_tac 1,
	Auto_tac]);

Goal "[|(h,l)::\\<preceq>(G,lT); h\\<le>|h'; G\\<turnstile>h h'\\<surd> |] ==> (h',l)::\\<preceq>(G,lT)";
by( fast_tac (HOL_cs addDs [conforms_localD] 
  addSEs [conformsI, lconf_hext]) 1);
qed "conforms_hext";

Goal "[|(h,l)::\\<preceq>(G, lT); G,h(a\\<mapsto>obj)\\<turnstile>obj\\<surd>; h\\<le>|h(a\\<mapsto>obj)|] ==> (h(a\\<mapsto>obj),l)::\\<preceq>(G, lT)";
by( rtac conforms_hext 1);
by   Auto_tac;
by( rtac hconfI 1);
by( dtac conforms_heapD 1);
by( (auto_tac (HOL_cs addEs [oconf_hext] addDs [hconfD],
		simpset()delsimps[split_paired_All])));
qed "conforms_upd_obj";

Goalw [conforms_def] 
"[|(h, l)::\\<preceq>(G, lT); G,h\\<turnstile>v::\\<preceq>T; lT va = Some T|] ==> \
\ (h, l(va\\<mapsto>v))::\\<preceq>(G, lT)";
by( auto_tac (claset() addEs [lconf_upd], simpset()));
qed "conforms_upd_local";
