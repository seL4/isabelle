(*  Title:      HOL/MicroJava/J/WellForm.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

Well-formedness of Java programs
for static checks on expressions and statements, see WellType.thy

improvements over Java Specification 1.0 (cf. 8.4.6.3, 8.4.6.4, 9.4.1):
* a method implementing or overwriting another method may have a result type 
  that widens to the result type of the other method (instead of identical type)

simplifications:
* for uniformity, Object is assumed to be declared like any other class
*)

theory WellForm = TypeRel:

types 'c wf_mb = "'c prog => cname => 'c mdecl => bool"

constdefs
 wf_fdecl :: "'c prog => fdecl => bool"
"wf_fdecl G == \<lambda>(fn,ft). is_type G ft"

 wf_mhead :: "'c prog => sig => ty => bool"
"wf_mhead G == \<lambda>(mn,pTs) rT. (\<forall>T\<in>set pTs. is_type G T) \<and> is_type G rT"

 wf_mdecl :: "'c wf_mb => 'c wf_mb"
"wf_mdecl wf_mb G C == \<lambda>(sig,rT,mb). wf_mhead G sig rT \<and> wf_mb G C (sig,rT,mb)"

 wf_cdecl :: "'c wf_mb => 'c prog => 'c cdecl => bool"
"wf_cdecl wf_mb G ==
   \<lambda>(C,(D,fs,ms)).
  (\<forall>f\<in>set fs. wf_fdecl G         f) \<and>  unique fs \<and>
  (\<forall>m\<in>set ms. wf_mdecl wf_mb G C m) \<and>  unique ms \<and>
  (C \<noteq> Object \<longrightarrow> is_class G D \<and>  \<not>G\<turnstile>D\<preceq>C C \<and>
                   (\<forall>(sig,rT,b)\<in>set ms. \<forall>D' rT' b'.
                      method(G,D) sig = Some(D',rT',b') --> G\<turnstile>rT\<preceq>rT'))"

 wf_prog :: "'c wf_mb => 'c prog => bool"
"wf_prog wf_mb G ==
   let cs = set G in ObjectC \<in> cs \<and> (\<forall>c\<in>cs. wf_cdecl wf_mb G c) \<and> unique G"

lemma class_wf: 
 "[|class G C = Some c; wf_prog wf_mb G|] ==> wf_cdecl wf_mb G (C,c)"
apply (unfold wf_prog_def class_def)
apply (simp)
apply (fast dest: map_of_SomeD)
done

lemma class_Object [simp]: 
	"wf_prog wf_mb G ==> class G Object = Some (arbitrary, [], [])"
apply (unfold wf_prog_def ObjectC_def class_def)
apply (auto intro: map_of_SomeI)
done

lemma is_class_Object [simp]: "wf_prog wf_mb G ==> is_class G Object"
apply (unfold is_class_def)
apply (simp (no_asm_simp))
done

lemma subcls1_wfD: "[|G\<turnstile>C\<prec>C1D; wf_prog wf_mb G|] ==> D \<noteq> C \<and> \<not>(D,C)\<in>(subcls1 G)^+"
apply( frule r_into_trancl)
apply( drule subcls1D)
apply(clarify)
apply( drule (1) class_wf)
apply( unfold wf_cdecl_def)
apply(force simp add: reflcl_trancl [THEN sym] simp del: reflcl_trancl)
done

lemma wf_cdecl_supD: 
"!!r. \<lbrakk>wf_cdecl wf_mb G (C,D,r); C \<noteq> Object\<rbrakk> \<Longrightarrow> is_class G D"
apply (unfold wf_cdecl_def)
apply (auto split add: option.split_asm)
done

lemma subcls_asym: "[|wf_prog wf_mb G; (C,D)\<in>(subcls1 G)^+|] ==> \<not>(D,C)\<in>(subcls1 G)^+"
apply(erule tranclE)
apply(fast dest!: subcls1_wfD )
apply(fast dest!: subcls1_wfD intro: trancl_trans)
done

lemma subcls_irrefl: "[|wf_prog wf_mb G; (C,D)\<in>(subcls1 G)^+|] ==> C \<noteq> D"
apply (erule trancl_trans_induct)
apply  (auto dest: subcls1_wfD subcls_asym)
done

lemma acyclic_subcls1: "wf_prog wf_mb G ==> acyclic (subcls1 G)"
apply (unfold acyclic_def)
apply (fast dest: subcls_irrefl)
done

lemma wf_subcls1: "wf_prog wf_mb G ==> wf ((subcls1 G)^-1)"
apply (rule finite_acyclic_wf)
apply ( subst finite_converse)
apply ( rule finite_subcls1)
apply (subst acyclic_converse)
apply (erule acyclic_subcls1)
done

lemma subcls_induct: 
"[|wf_prog wf_mb G; !!C. \<forall>D. (C,D)\<in>(subcls1 G)^+ --> P D ==> P C|] ==> P C"
(is "?A \<Longrightarrow> PROP ?P \<Longrightarrow> _")
proof -
  assume p: "PROP ?P"
  assume ?A thus ?thesis apply -
apply(drule wf_subcls1)
apply(drule wf_trancl)
apply(simp only: trancl_converse)
apply(erule_tac a = C in wf_induct)
apply(rule p)
apply(auto)
done
qed

lemma subcls1_induct:
"[|is_class G C; wf_prog wf_mb G; P Object;  
   !!C D fs ms. [|C \<noteq> Object; is_class G C; class G C = Some (D,fs,ms) \<and>  
    wf_cdecl wf_mb G (C,D,fs,ms) \<and> G\<turnstile>C\<prec>C1D \<and> is_class G D \<and> P D|] ==> P C 
 |] ==> P C"
(is "?A \<Longrightarrow> ?B \<Longrightarrow> ?C \<Longrightarrow> PROP ?P \<Longrightarrow> _")
proof -
  assume p: "PROP ?P"
  assume ?A ?B ?C thus ?thesis apply -
apply(unfold is_class_def)
apply( rule impE)
prefer 2
apply(   assumption)
prefer 2
apply(  assumption)
apply( erule thin_rl)
apply( rule subcls_induct)
apply(  assumption)
apply( rule impI)
apply( case_tac "C = Object")
apply(  fast)
apply safe
apply( frule (1) class_wf)
apply( frule (1) wf_cdecl_supD)

apply( subgoal_tac "G\<turnstile>C\<prec>C1a")
apply( erule_tac [2] subcls1I)
apply(  rule p)
apply (unfold is_class_def)
apply auto
done
qed

lemmas method_rec = wf_subcls1 [THEN [2] method_rec_lemma];

lemmas fields_rec = wf_subcls1 [THEN [2] fields_rec_lemma];

lemma method_Object [simp]: "wf_prog wf_mb G ==> method (G,Object) = empty"
apply(subst method_rec)
apply auto
done

lemma fields_Object [simp]: "wf_prog wf_mb G ==> fields (G,Object) = []"
apply(subst fields_rec)
apply auto
done

lemma field_Object [simp]: "wf_prog wf_mb G ==> field (G,Object) = empty"
apply (unfold field_def)
apply(simp (no_asm_simp))
done

lemma subcls_C_Object: "[|is_class G C; wf_prog wf_mb G|] ==> G\<turnstile>C\<preceq>C Object"
apply(erule subcls1_induct)
apply(  assumption)
apply( fast)
apply(auto dest!: wf_cdecl_supD)
apply(erule (1) rtrancl_into_rtrancl2)
done

lemma is_type_rTI: "wf_mhead G sig rT ==> is_type G rT"
apply (unfold wf_mhead_def)
apply auto
done

lemma widen_fields_defpl': "[|is_class G C; wf_prog wf_mb G|] ==>  
  \<forall>((fn,fd),fT)\<in>set (fields (G,C)). G\<turnstile>C\<preceq>C fd"
apply( erule subcls1_induct)
apply(   assumption)
apply(  simp (no_asm_simp))
apply( tactic "safe_tac HOL_cs")
apply( subst fields_rec)
apply(   assumption)
apply(  assumption)
apply( simp (no_asm) split del: split_if)
apply( rule ballI)
apply( simp (no_asm_simp) only: split_tupled_all)
apply( simp (no_asm))
apply( erule UnE)
apply(  force)
apply( erule r_into_rtrancl [THEN rtrancl_trans])
apply auto
done

lemma widen_fields_defpl: "[|((fn,fd),fT) \<in> set (fields (G,C)); wf_prog wf_mb G; is_class G C|] ==>  
  G\<turnstile>C\<preceq>C fd"
apply( drule (1) widen_fields_defpl')
apply (fast)
done

lemma unique_fields: "[|is_class G C; wf_prog wf_mb G|] ==> unique (fields (G,C))"
apply( erule subcls1_induct)
apply(   assumption)
apply(  safe dest!: wf_cdecl_supD)
apply(  simp (no_asm_simp))
apply( drule subcls1_wfD)
apply(  assumption)
apply( subst fields_rec)
apply   auto
apply( rotate_tac -1)
apply( frule class_wf)
apply  auto
apply( simp add: wf_cdecl_def)
apply( erule unique_append)
apply(  rule unique_map_inj)
apply(   clarsimp)
apply  (rule injI)
apply(  simp)
apply(auto dest!: widen_fields_defpl)
done

lemma fields_mono_lemma [rule_format (no_asm)]: "[|wf_prog wf_mb G; (C',C)\<in>(subcls1 G)^*|] ==>  
  x \<in> set (fields (G,C)) --> x \<in> set (fields (G,C'))"
apply(erule converse_rtrancl_induct)
apply( safe dest!: subcls1D)
apply(subst fields_rec)
apply(  auto)
done

lemma fields_mono: 
"\<lbrakk>map_of (fields (G,C)) fn = Some f; G\<turnstile>D\<preceq>C C; is_class G D; wf_prog wf_mb G\<rbrakk> 
  \<Longrightarrow> map_of (fields (G,D)) fn = Some f"
apply (rule map_of_SomeI)
apply  (erule (1) unique_fields)
apply (erule (1) fields_mono_lemma)
apply (erule map_of_SomeD)
done

lemma widen_cfs_fields: 
"[|field (G,C) fn = Some (fd, fT); G\<turnstile>D\<preceq>C C; wf_prog wf_mb G|]==>  
  map_of (fields (G,D)) (fn, fd) = Some fT"
apply (drule field_fields)
apply (drule rtranclD)
apply safe
apply (frule subcls_is_class)
apply (drule trancl_into_rtrancl)
apply (fast dest: fields_mono)
done

lemma method_wf_mdecl [rule_format (no_asm)]: "wf_prog wf_mb G ==> is_class G C \<Longrightarrow>   
     method (G,C) sig = Some (md,mh,m) 
   --> G\<turnstile>C\<preceq>C md \<and> wf_mdecl wf_mb G md (sig,(mh,m))"
apply( erule subcls1_induct)
apply(   assumption)
apply(  force)
apply( clarify)
apply( frule_tac C = C in method_rec)
apply(  assumption)
apply( rotate_tac -1)
apply( simp)
apply( drule override_SomeD)
apply( erule disjE)
apply(  erule_tac V = "?P --> ?Q" in thin_rl)
apply (frule map_of_SomeD)
apply (clarsimp simp add: wf_cdecl_def)
apply( clarify)
apply( rule rtrancl_trans)
prefer 2
apply(  assumption)
apply( rule r_into_rtrancl)
apply( fast intro: subcls1I)
done

lemma subcls_widen_methd [rule_format (no_asm)]: 
  "[|G\<turnstile>T\<preceq>C T'; wf_prog wf_mb G|] ==>  
   \<forall>D rT b. method (G,T') sig = Some (D,rT ,b) --> 
  (\<exists>D' rT' b'. method (G,T) sig = Some (D',rT',b') \<and> G\<turnstile>rT'\<preceq>rT)"
apply( drule rtranclD)
apply( erule disjE)
apply(  fast)
apply( erule conjE)
apply( erule trancl_trans_induct)
prefer 2
apply(  clarify)
apply(  drule spec, drule spec, drule spec, erule (1) impE)
apply(  fast elim: widen_trans)
apply( clarify)
apply( drule subcls1D)
apply( clarify)
apply( subst method_rec)
apply(  assumption)
apply( unfold override_def)
apply( simp (no_asm_simp) del: split_paired_Ex)
apply( case_tac "\<exists>z. map_of(map (\<lambda>(s,m). (s, ?C, m)) ms) sig = Some z")
apply(  erule exE)
apply(  rotate_tac -1, frule ssubst, erule_tac [2] asm_rl)
prefer 2
apply(  rotate_tac -1, frule ssubst, erule_tac [2] asm_rl)
apply(  tactic "asm_full_simp_tac (HOL_ss addsimps [not_None_eq RS sym]) 1")
apply(  simp_all (no_asm_simp) del: split_paired_Ex)
apply( drule (1) class_wf)
apply( simp (no_asm_simp) only: split_tupled_all)
apply( unfold wf_cdecl_def)
apply( drule map_of_SomeD)
apply auto
done

lemma subtype_widen_methd: 
 "[| G\<turnstile> C\<preceq>C D; wf_prog wf_mb G;  
     method (G,D) sig = Some (md, rT, b) |]  
  ==> \<exists>mD' rT' b'. method (G,C) sig= Some(mD',rT',b') \<and> G\<turnstile>rT'\<preceq>rT"
apply(auto dest: subcls_widen_methd method_wf_mdecl simp add: wf_mdecl_def wf_mhead_def split_def)
done

lemma method_in_md [rule_format (no_asm)]: "wf_prog wf_mb G ==> is_class G C \<Longrightarrow> \<forall>D. method (G,C) sig = Some(D,mh,code) --> is_class G D \<and> method (G,D) sig = Some(D,mh,code)"
apply (erule (1) subcls1_induct)
 apply (simp)
apply (erule conjE)
apply (subst method_rec)
  apply (assumption)
 apply (assumption)
apply (clarify)
apply (erule_tac "x" = "Da" in allE)
apply (clarsimp)
 apply (simp add: map_of_map)
 apply (clarify)
 apply (subst method_rec)
   apply (assumption)
  apply (assumption)
 apply (simp add: override_def map_of_map split add: option.split)
done

lemma widen_methd: 
"[| method (G,C) sig = Some (md,rT,b); wf_prog wf_mb G; G\<turnstile>T''\<preceq>C C|] 
  ==> \<exists>md' rT' b'. method (G,T'') sig = Some (md',rT',b') \<and> G\<turnstile>rT'\<preceq>rT"
apply( drule subcls_widen_methd)
apply   auto
done

lemma Call_lemma: 
"[|method (G,C) sig = Some (md,rT,b); G\<turnstile>T''\<preceq>C C; wf_prog wf_mb G;  
  class G C = Some y|] ==> \<exists>T' rT' b. method (G,T'') sig = Some (T',rT',b) \<and>  
  G\<turnstile>rT'\<preceq>rT \<and> G\<turnstile>T''\<preceq>C T' \<and> wf_mhead G sig rT' \<and> wf_mb G T' (sig,rT',b)"
apply( drule (2) widen_methd)
apply( clarify)
apply( frule subcls_is_class2)
apply (unfold is_class_def)
apply (simp (no_asm_simp))
apply( drule method_wf_mdecl)
apply( unfold wf_mdecl_def)
apply( unfold is_class_def)
apply auto
done


lemma fields_is_type_lemma [rule_format (no_asm)]: "[|is_class G C; wf_prog wf_mb G|] ==>  
  \<forall>f\<in>set (fields (G,C)). is_type G (snd f)"
apply( erule (1) subcls1_induct)
apply(  simp (no_asm_simp))
apply( subst fields_rec)
apply(   fast)
apply(  assumption)
apply( clarsimp)
apply( safe)
prefer 2
apply(  force)
apply( drule (1) class_wf)
apply( unfold wf_cdecl_def)
apply( clarsimp)
apply( drule (1) bspec)
apply( unfold wf_fdecl_def)
apply auto
done

lemma fields_is_type: "[|map_of (fields (G,C)) fn = Some f; wf_prog wf_mb G; is_class G C|] ==>  
  is_type G f"
apply(drule map_of_SomeD)
apply(drule (2) fields_is_type_lemma)
apply(auto)
done

lemma methd:
  "[| wf_prog wf_mb G; (C,S,fs,mdecls) \<in> set G; (sig,rT,code) \<in> set mdecls |]
  ==> method (G,C) sig = Some(C,rT,code) \<and> is_class G C"
proof -
  assume wf: "wf_prog wf_mb G" 
  assume C:  "(C,S,fs,mdecls) \<in> set G"

  assume m: "(sig,rT,code) \<in> set mdecls"
  moreover
  from wf
  have "class G Object = Some (arbitrary, [], [])"
    by simp 
  moreover
  from wf C
  have c: "class G C = Some (S,fs,mdecls)"
    by (auto simp add: wf_prog_def class_def is_class_def intro: map_of_SomeI)
  ultimately
  have O: "C \<noteq> Object"
    by auto
      
  from wf C
  have "unique mdecls"
    by (unfold wf_prog_def wf_cdecl_def) auto

  hence "unique (map (\<lambda>(s,m). (s,C,m)) mdecls)"
    by - (induct mdecls, auto)

  with m
  have "map_of (map (\<lambda>(s,m). (s,C,m)) mdecls) sig = Some (C,rT,code)"
    by (force intro: map_of_SomeI)

  with wf C m c O
  show ?thesis
    by (auto simp add: is_class_def dest: method_rec)
qed

end
