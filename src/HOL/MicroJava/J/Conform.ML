(*  Title:      HOL/MicroJava/J/Conform.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

section "hext";

Goalw [hext_def] 
" \\<forall>a C fs . h  a = Some (C,fs) -->  \
\     (\\<exists>fs'. h' a = Some (C,fs')) ==> h\\<le>|h'"; 
by Auto_tac;
qed "hextI";

Goalw [hext_def] "[|h\\<le>|h'; h a = Some (C,fs) |] ==> \\<exists>fs'. h' a = Some (C,fs')";
by (Force_tac 1);
qed "hext_objD";

Goal "h\\<le>|h";
by (rtac hextI 1);
by (Fast_tac 1);
qed "hext_refl";

Goal "h a = None ==> h\\<le>|h(a\\<mapsto>x)";
by (rtac hextI 1);
by Auto_tac;
qed "hext_new";

Goal "[|h\\<le>|h'; h'\\<le>|h''|] ==> h\\<le>|h''";
by (rtac hextI 1);
by (fast_tac (HOL_cs addDs [hext_objD]) 1);
qed "hext_trans";

Addsimps [hext_refl, hext_new];

Goal "h a = Some (C,fs) ==> h\\<le>|h(a\\<mapsto>(C,fs'))";
by (rtac hextI 1);
by Auto_tac;
qed "hext_upd_obj";


section "conf";

Goalw [conf_def] "G,h\\<turnstile>Null::\\<preceq>T = G\\<turnstile>RefT NullT\\<preceq>T"; 
by (Simp_tac 1);
qed "conf_Null";
Addsimps [conf_Null];

Goalw [conf_def] "typeof (\\<lambda>v. None) v = Some T --> G,h\\<turnstile>v::\\<preceq>T";
by (rtac val_.induct 1);
by Auto_tac;
qed_spec_mp "conf_litval";
Addsimps[conf_litval];

Goalw [conf_def] "[|h a = Some obj; G\\<turnstile>obj_ty obj\\<preceq>T|] ==> G,h\\<turnstile>Addr a::\\<preceq>T";
by (Asm_full_simp_tac 1);
qed "conf_AddrI";

Goalw [conf_def] "[|h a = Some (C,fs); G\\<turnstile>C\\<preceq>C D|] ==> G,h\\<turnstile>Addr a::\\<preceq> Class D"; 
by (Asm_full_simp_tac 1);
qed "conf_obj_AddrI";

Goalw [conf_def] "is_type G T --> G,h\\<turnstile>default_val T::\\<preceq>T";
by (res_inst_tac [("y","T")] ty.exhaust 1);
by  (etac ssubst 1);
by  (res_inst_tac [("y","prim_ty")] prim_ty.exhaust 1);
by    (auto_tac (claset(), simpset() addsimps [widen.null]));
qed_spec_mp "defval_conf";

Goalw [conf_def] 
"h a = Some (C,fs) ==> (G,h(a\\<mapsto>(C,fs'))\\<turnstile>x::\\<preceq>T) = (G,h\\<turnstile>x::\\<preceq>T)";
by (rtac val_.induct 1);
by Auto_tac;
qed "conf_upd_obj";

Goalw [conf_def] "wf_prog wf_mb G ==> G,h\\<turnstile>x::\\<preceq>T --> G\\<turnstile>T\\<preceq>T' --> G,h\\<turnstile>x::\\<preceq>T'";
by (rtac val_.induct 1);
by (auto_tac (claset() addIs [widen_trans], simpset()));
qed_spec_mp "conf_widen";

Goalw [conf_def] "h\\<le>|h' ==> G,h\\<turnstile>v::\\<preceq>T --> G,h'\\<turnstile>v::\\<preceq>T";
by (rtac val_.induct 1);
by (auto_tac (claset() addDs [hext_objD], simpset()));
qed_spec_mp "conf_hext";

Goalw [conf_def] "[|h a = None; G,h\\<turnstile>Addr t::\\<preceq>T|] ==> t\\<noteq>a";
by Auto_tac;
qed "new_locD";

Goalw [conf_def]
 "G,h\\<turnstile>a'::\\<preceq>RefT T --> a' = Null |  \
\ (\\<exists>a obj T'. a' = Addr a \\<and>  h a = Some obj \\<and>  obj_ty obj = T' \\<and>  G\\<turnstile>T'\\<preceq>RefT T)";
by(induct_tac "a'" 1);
by(Auto_tac);
qed_spec_mp "conf_RefTD";

Goal "G,h\\<turnstile>a'::\\<preceq>RefT NullT ==> a' = Null";
by (dtac conf_RefTD 1);
by Auto_tac;
qed "conf_NullTD";

Goal "[|a' \\<noteq> Null; G,h\\<turnstile>a'::\\<preceq>RefT t|] ==> \
\ \\<exists>a C fs. a' = Addr a \\<and>  h a = Some (C,fs) \\<and>  G\\<turnstile>Class C\\<preceq>RefT t";
by (dtac conf_RefTD 1);
by Auto_tac;
qed "non_npD";

Goal "!!G. [|a' \\<noteq> Null; G,h\\<turnstile>a'::\\<preceq> Class C; C \\<noteq> Object|] ==> \
\ (\\<exists>a C' fs. a' = Addr a \\<and>  h a = Some (C',fs) \\<and>  G\\<turnstile>C'\\<preceq>C C)";
by (fast_tac (claset() addDs [non_npD]) 1);
qed "non_np_objD";

Goal "a' \\<noteq> Null ==> wf_prog wf_mb G ==> G,h\\<turnstile>a'::\\<preceq>RefT t -->\
\ (\\<forall>C. t = ClassT C --> C \\<noteq> Object) --> \
\ (\\<exists>a C fs. a' = Addr a \\<and>  h a = Some (C,fs) \\<and>  G\\<turnstile>Class C\\<preceq>RefT t)";
by(res_inst_tac [("y","t")] ref_ty.exhaust 1);
 by (fast_tac (claset() addDs [conf_NullTD]) 1);
by (fast_tac (claset() addDs [non_np_objD]) 1);
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

Goalw[lconf_def] "[| G,h\\<turnstile>vs[::\\<preceq>]Ts; Ts n = Some T |] ==> G,h\\<turnstile>(the (vs n))::\\<preceq>T";
by (Force_tac 1);
qed "lconfD";

Goalw [lconf_def] "[| G,h\\<turnstile>l[::\\<preceq>]L; h\\<le>|h' |] ==> G,h'\\<turnstile>l[::\\<preceq>]L";
by  (fast_tac (claset() addEs [conf_hext]) 1);
qed "lconf_hext";
AddEs [lconf_hext];

Goalw [lconf_def] "!!X. [| G,h\\<turnstile>l[::\\<preceq>]lT; \
\ G,h\\<turnstile>v::\\<preceq>T; lT va = Some T |] ==> G,h\\<turnstile>l(va\\<mapsto>v)[::\\<preceq>]lT";
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

Goalw [lconf_def] "[|G,s\\<turnstile>l[::\\<preceq>]L; G,s\\<turnstile>v::\\<preceq>T|] ==> G,s\\<turnstile>l(vn\\<mapsto>v)[::\\<preceq>]L(vn\\<mapsto>T)";
by Auto_tac;
qed "lconf_ext";

Goalw [lconf_def] "G,h\\<turnstile>l[::\\<preceq>]L ==> \\<forall>vs Ts. nodups vns --> length Ts = length vns --> list_all2 (\\<lambda>v T. G,h\\<turnstile>v::\\<preceq>T) vs Ts --> G,h\\<turnstile>l(vns[\\<mapsto>]vs)[::\\<preceq>]L(vns[\\<mapsto>]Ts)";
by( induct_tac "vns" 1);
by(  ALLGOALS Clarsimp_tac);
by( forward_tac [list_all2_lengthD] 1);
by( auto_tac (claset(), simpset() addsimps [length_Suc_conv]));
qed_spec_mp "lconf_ext_list";


section "oconf";

Goalw [oconf_def] "G,h\\<turnstile>obj\\<surd> ==> h\\<le>|h' ==> G,h'\\<turnstile>obj\\<surd>"; 
by (Fast_tac 1);
qed "oconf_hext";

Goalw [oconf_def,lconf_def] "G,h\\<turnstile>(C,fs)\\<surd> = \
\ (\\<forall>T f. map_of(fields (G,C)) f = Some T --> (\\<exists>v. fs f = Some v \\<and>  G,h\\<turnstile>v::\\<preceq>T))";
by Auto_tac;
qed "oconf_obj";
bind_thm ("oconf_objD", oconf_obj RS iffD1 RS spec RS spec RS mp);


section "hconf";

Goalw [hconf_def] "[|G\\<turnstile>h h\\<surd>; h a = Some obj|] ==> G,h\\<turnstile>obj\\<surd>";
by (Fast_tac 1);
qed "hconfD";

Goalw [hconf_def] "\\<forall>a obj. h a=Some obj --> G,h\\<turnstile>obj\\<surd> ==> G\\<turnstile>h h\\<surd>";
by (Fast_tac 1);
qed "hconfI";


section "conforms";

Goalw [conforms_def] "(h, l)::\\<preceq>(G, lT) ==> G\\<turnstile>h h\\<surd>";
by (Asm_full_simp_tac 1);
qed "conforms_heapD";

Goalw [conforms_def] "(h, l)::\\<preceq>(G, lT) ==> G,h\\<turnstile>l[::\\<preceq>]lT";
by (Asm_full_simp_tac 1);
qed "conforms_localD";

Goalw [conforms_def] "[|G\\<turnstile>h h\\<surd>; G,h\\<turnstile>l[::\\<preceq>]lT|] ==> (h, l)::\\<preceq>(G, lT)"; 
by Auto_tac;
qed "conformsI";

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
