(*  Title:      HOL/MicroJava/J/Conform.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header "Conformity Relations for Type Soundness Proof"

theory Conform = State + WellType:

types 'c env_ = "'c prog \<times> (vname \<leadsto> ty)"  -- "same as @{text env} of @{text WellType.thy}"

constdefs

  hext :: "aheap => aheap => bool" ("_ <=| _" [51,51] 50)
 "h<=|h' == \<forall>a C fs. h a = Some(C,fs) --> (\<exists>fs'. h' a = Some(C,fs'))"

  conf :: "'c prog => aheap => val => ty => bool" 
                                   ("_,_ |- _ ::<= _"  [51,51,51,51] 50)
 "G,h|-v::<=T == \<exists>T'. typeof (option_map obj_ty o h) v = Some T' \<and> G\<turnstile>T'\<preceq>T"

  lconf :: "'c prog => aheap => ('a \<leadsto> val) => ('a \<leadsto> ty) => bool"
                                   ("_,_ |- _ [::<=] _" [51,51,51,51] 50)
 "G,h|-vs[::<=]Ts == \<forall>n T. Ts n = Some T --> (\<exists>v. vs n = Some v \<and> G,h|-v::<=T)"

  oconf :: "'c prog => aheap => obj => bool" ("_,_ |- _ [ok]" [51,51,51] 50)
 "G,h|-obj [ok] == G,h|-snd obj[::<=]map_of (fields (G,fst obj))"

  hconf :: "'c prog => aheap => bool" ("_ |-h _ [ok]" [51,51] 50)
 "G|-h h [ok]    == \<forall>a obj. h a = Some obj --> G,h|-obj [ok]"

  conforms :: "state => java_mb env_ => bool" ("_ ::<= _" [51,51] 50)
 "s::<=E == prg E|-h heap s [ok] \<and> prg E,heap s|-locals s[::<=]localT E"


syntax (xsymbols)
  hext     :: "aheap => aheap => bool"
              ("_ \<le>| _" [51,51] 50)

  conf     :: "'c prog => aheap => val => ty => bool"
              ("_,_ \<turnstile> _ ::\<preceq> _" [51,51,51,51] 50)

  lconf    :: "'c prog => aheap => ('a \<leadsto> val) => ('a \<leadsto> ty) => bool"
              ("_,_ \<turnstile> _ [::\<preceq>] _" [51,51,51,51] 50)

  oconf    :: "'c prog => aheap => obj => bool"
              ("_,_ \<turnstile> _ \<surd>" [51,51,51] 50)

  hconf    :: "'c prog => aheap => bool"
              ("_ \<turnstile>h _ \<surd>" [51,51] 50)

  conforms :: "state => java_mb env_ => bool"
              ("_ ::\<preceq> _" [51,51] 50)


section "hext"

lemma hextI: 
" \<forall>a C fs . h  a = Some (C,fs) -->   
      (\<exists>fs'. h' a = Some (C,fs')) ==> h\<le>|h'"
apply (unfold hext_def)
apply auto
done

lemma hext_objD: "[|h\<le>|h'; h a = Some (C,fs) |] ==> \<exists>fs'. h' a = Some (C,fs')"
apply (unfold hext_def)
apply (force)
done

lemma hext_refl [simp]: "h\<le>|h"
apply (rule hextI)
apply (fast)
done

lemma hext_new [simp]: "h a = None ==> h\<le>|h(a\<mapsto>x)"
apply (rule hextI)
apply auto
done

lemma hext_trans: "[|h\<le>|h'; h'\<le>|h''|] ==> h\<le>|h''"
apply (rule hextI)
apply (fast dest: hext_objD)
done

lemma hext_upd_obj: "h a = Some (C,fs) ==> h\<le>|h(a\<mapsto>(C,fs'))"
apply (rule hextI)
apply auto
done


section "conf"

lemma conf_Null [simp]: "G,h\<turnstile>Null::\<preceq>T = G\<turnstile>RefT NullT\<preceq>T"
apply (unfold conf_def)
apply (simp (no_asm))
done

lemma conf_litval [rule_format (no_asm), simp]: 
  "typeof (\<lambda>v. None) v = Some T --> G,h\<turnstile>v::\<preceq>T"
apply (unfold conf_def)
apply (rule val.induct)
apply auto
done

lemma conf_AddrI: "[|h a = Some obj; G\<turnstile>obj_ty obj\<preceq>T|] ==> G,h\<turnstile>Addr a::\<preceq>T"
apply (unfold conf_def)
apply (simp)
done

lemma conf_obj_AddrI: "[|h a = Some (C,fs); G\<turnstile>C\<preceq>C D|] ==> G,h\<turnstile>Addr a::\<preceq> Class D"
apply (unfold conf_def)
apply (simp)
done

lemma defval_conf [rule_format (no_asm)]: 
  "is_type G T --> G,h\<turnstile>default_val T::\<preceq>T"
apply (unfold conf_def)
apply (rule_tac "y" = "T" in ty.exhaust)
apply  (erule ssubst)
apply  (rule_tac "y" = "prim_ty" in prim_ty.exhaust)
apply    (auto simp add: widen.null)
done

lemma conf_upd_obj: 
"h a = Some (C,fs) ==> (G,h(a\<mapsto>(C,fs'))\<turnstile>x::\<preceq>T) = (G,h\<turnstile>x::\<preceq>T)"
apply (unfold conf_def)
apply (rule val.induct)
apply auto
done

lemma conf_widen [rule_format (no_asm)]: 
  "wf_prog wf_mb G ==> G,h\<turnstile>x::\<preceq>T --> G\<turnstile>T\<preceq>T' --> G,h\<turnstile>x::\<preceq>T'"
apply (unfold conf_def)
apply (rule val.induct)
apply (auto intro: widen_trans)
done

lemma conf_hext [rule_format (no_asm)]: "h\<le>|h' ==> G,h\<turnstile>v::\<preceq>T --> G,h'\<turnstile>v::\<preceq>T"
apply (unfold conf_def)
apply (rule val.induct)
apply (auto dest: hext_objD)
done

lemma new_locD: "[|h a = None; G,h\<turnstile>Addr t::\<preceq>T|] ==> t\<noteq>a"
apply (unfold conf_def)
apply auto
done

lemma conf_RefTD [rule_format (no_asm)]: 
 "G,h\<turnstile>a'::\<preceq>RefT T --> a' = Null |   
  (\<exists>a obj T'. a' = Addr a \<and>  h a = Some obj \<and>  obj_ty obj = T' \<and>  G\<turnstile>T'\<preceq>RefT T)"
apply (unfold conf_def)
apply(induct_tac "a'")
apply(auto)
done

lemma conf_NullTD: "G,h\<turnstile>a'::\<preceq>RefT NullT ==> a' = Null"
apply (drule conf_RefTD)
apply auto
done

lemma non_npD: "[|a' \<noteq> Null; G,h\<turnstile>a'::\<preceq>RefT t|] ==>  
  \<exists>a C fs. a' = Addr a \<and>  h a = Some (C,fs) \<and>  G\<turnstile>Class C\<preceq>RefT t"
apply (drule conf_RefTD)
apply auto
done

lemma non_np_objD: "!!G. [|a' \<noteq> Null; G,h\<turnstile>a'::\<preceq> Class C; C \<noteq> Object|] ==>  
  (\<exists>a C' fs. a' = Addr a \<and>  h a = Some (C',fs) \<and>  G\<turnstile>C'\<preceq>C C)"
apply (fast dest: non_npD)
done

lemma non_np_objD' [rule_format (no_asm)]: 
  "a' \<noteq> Null ==> wf_prog wf_mb G ==> G,h\<turnstile>a'::\<preceq>RefT t --> 
  (\<forall>C. t = ClassT C --> C \<noteq> Object) -->  
  (\<exists>a C fs. a' = Addr a \<and>  h a = Some (C,fs) \<and>  G\<turnstile>Class C\<preceq>RefT t)"
apply(rule_tac "y" = "t" in ref_ty.exhaust)
 apply (fast dest: conf_NullTD)
apply (fast dest: non_np_objD)
done

lemma conf_list_gext_widen [rule_format (no_asm)]: 
  "wf_prog wf_mb G ==> \<forall>Ts Ts'. list_all2 (conf G h) vs Ts --> 
  list_all2 (\<lambda>T T'. G\<turnstile>T\<preceq>T') Ts Ts' -->  list_all2 (conf G h) vs Ts'"
apply(induct_tac "vs")
 apply(clarsimp)
apply(clarsimp)
apply(frule list_all2_lengthD [THEN sym])
apply(simp (no_asm_use) add: length_Suc_conv)
apply(safe)
apply(frule list_all2_lengthD [THEN sym])
apply(simp (no_asm_use) add: length_Suc_conv)
apply(clarify)
apply(fast elim: conf_widen)
done


section "lconf"

lemma lconfD: "[| G,h\<turnstile>vs[::\<preceq>]Ts; Ts n = Some T |] ==> G,h\<turnstile>(the (vs n))::\<preceq>T"
apply (unfold lconf_def)
apply (force)
done

lemma lconf_hext [elim]: "[| G,h\<turnstile>l[::\<preceq>]L; h\<le>|h' |] ==> G,h'\<turnstile>l[::\<preceq>]L"
apply (unfold lconf_def)
apply  (fast elim: conf_hext)
done

lemma lconf_upd: "!!X. [| G,h\<turnstile>l[::\<preceq>]lT;  
  G,h\<turnstile>v::\<preceq>T; lT va = Some T |] ==> G,h\<turnstile>l(va\<mapsto>v)[::\<preceq>]lT"
apply (unfold lconf_def)
apply auto
done

lemma lconf_init_vars_lemma [rule_format (no_asm)]: 
  "\<forall>x. P x --> R (dv x) x ==> (\<forall>x. map_of fs f = Some x --> P x) -->  
  (\<forall>T. map_of fs f = Some T -->  
  (\<exists>v. map_of (map (\<lambda>(f,ft). (f, dv ft)) fs) f = Some v \<and>  R v T))"
apply( induct_tac "fs")
apply auto
done

lemma lconf_init_vars [intro!]: 
"\<forall>n. \<forall>T. map_of fs n = Some T --> is_type G T ==> G,h\<turnstile>init_vars fs[::\<preceq>]map_of fs"
apply (unfold lconf_def init_vars_def)
apply auto
apply( rule lconf_init_vars_lemma)
apply(   erule_tac [3] asm_rl)
apply(  intro strip)
apply(  erule defval_conf)
apply auto
done

lemma lconf_ext: "[|G,s\<turnstile>l[::\<preceq>]L; G,s\<turnstile>v::\<preceq>T|] ==> G,s\<turnstile>l(vn\<mapsto>v)[::\<preceq>]L(vn\<mapsto>T)"
apply (unfold lconf_def)
apply auto
done

lemma lconf_ext_list [rule_format (no_asm)]: 
  "G,h\<turnstile>l[::\<preceq>]L ==> \<forall>vs Ts. distinct vns --> length Ts = length vns --> 
  list_all2 (\<lambda>v T. G,h\<turnstile>v::\<preceq>T) vs Ts --> G,h\<turnstile>l(vns[\<mapsto>]vs)[::\<preceq>]L(vns[\<mapsto>]Ts)"
apply (unfold lconf_def)
apply( induct_tac "vns")
apply(  clarsimp)
apply( clarsimp)
apply( frule list_all2_lengthD)
apply( auto simp add: length_Suc_conv)
done


section "oconf"

lemma oconf_hext: "G,h\<turnstile>obj\<surd> ==> h\<le>|h' ==> G,h'\<turnstile>obj\<surd>"
apply (unfold oconf_def)
apply (fast)
done

lemma oconf_obj: "G,h\<turnstile>(C,fs)\<surd> =  
  (\<forall>T f. map_of(fields (G,C)) f = Some T --> (\<exists>v. fs f = Some v \<and>  G,h\<turnstile>v::\<preceq>T))"
apply (unfold oconf_def lconf_def)
apply auto
done

lemmas oconf_objD = oconf_obj [THEN iffD1, THEN spec, THEN spec, THEN mp]


section "hconf"

lemma hconfD: "[|G\<turnstile>h h\<surd>; h a = Some obj|] ==> G,h\<turnstile>obj\<surd>"
apply (unfold hconf_def)
apply (fast)
done

lemma hconfI: "\<forall>a obj. h a=Some obj --> G,h\<turnstile>obj\<surd> ==> G\<turnstile>h h\<surd>"
apply (unfold hconf_def)
apply (fast)
done


section "conforms"

lemma conforms_heapD: "(h, l)::\<preceq>(G, lT) ==> G\<turnstile>h h\<surd>"
apply (unfold conforms_def)
apply (simp)
done

lemma conforms_localD: "(h, l)::\<preceq>(G, lT) ==> G,h\<turnstile>l[::\<preceq>]lT"
apply (unfold conforms_def)
apply (simp)
done

lemma conformsI: "[|G\<turnstile>h h\<surd>; G,h\<turnstile>l[::\<preceq>]lT|] ==> (h, l)::\<preceq>(G, lT)"
apply (unfold conforms_def)
apply auto
done

lemma conforms_hext: "[|(h,l)::\<preceq>(G,lT); h\<le>|h'; G\<turnstile>h h'\<surd> |] ==> (h',l)::\<preceq>(G,lT)"
apply( fast dest: conforms_localD elim!: conformsI lconf_hext)
done

lemma conforms_upd_obj: 
  "[|(h,l)::\<preceq>(G, lT); G,h(a\<mapsto>obj)\<turnstile>obj\<surd>; h\<le>|h(a\<mapsto>obj)|] ==> (h(a\<mapsto>obj),l)::\<preceq>(G, lT)"
apply(rule conforms_hext)
apply  auto
apply(rule hconfI)
apply(drule conforms_heapD)
apply(tactic {* auto_tac (HOL_cs addEs [thm "oconf_hext"] 
                addDs [thm "hconfD"], simpset() delsimps [split_paired_All]) *})
done

lemma conforms_upd_local: 
"[|(h, l)::\<preceq>(G, lT); G,h\<turnstile>v::\<preceq>T; lT va = Some T|] ==> (h, l(va\<mapsto>v))::\<preceq>(G, lT)"
apply (unfold conforms_def)
apply( auto elim: lconf_upd)
done

end
