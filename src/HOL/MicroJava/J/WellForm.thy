(*  Title:      HOL/MicroJava/J/WellForm.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Well-formedness of Java programs} *}

theory WellForm = TypeRel + SystemClasses:

text {*
for static checks on expressions and statements, see WellType.

\begin{description}
\item[improvements over Java Specification 1.0 (cf. 8.4.6.3, 8.4.6.4, 9.4.1):]\ \\
\begin{itemize}
\item a method implementing or overwriting another method may have a result type
that widens to the result type of the other method (instead of identical type)
\end{itemize}

\item[simplifications:]\ \\
\begin{itemize}
\item for uniformity, Object is assumed to be declared like any other class
\end{itemize}
\end{description}
*}
types 'c wf_mb = "'c prog => cname => 'c mdecl => bool"

constdefs
 wf_syscls :: "'c prog => bool"
"wf_syscls G == let cs = set G in Object \<in> fst ` cs \<and> (\<forall>x. Xcpt x \<in> fst ` cs)"

 wf_fdecl :: "'c prog => fdecl => bool"
"wf_fdecl G == \<lambda>(fn,ft). is_type G ft"

 wf_mhead :: "'c prog => sig => ty => bool"
"wf_mhead G == \<lambda>(mn,pTs) rT. (\<forall>T\<in>set pTs. is_type G T) \<and> is_type G rT"

 ws_cdecl :: "'c prog => 'c cdecl => bool"
"ws_cdecl G ==
   \<lambda>(C,(D,fs,ms)).
  (\<forall>f\<in>set fs. wf_fdecl G         f) \<and>  unique fs \<and>
  (\<forall>(sig,rT,mb)\<in>set ms. wf_mhead G sig rT) \<and> unique ms \<and>
  (C \<noteq> Object \<longrightarrow> is_class G D \<and>  \<not>G\<turnstile>D\<preceq>C C)"

 ws_prog :: "'c prog => bool"
"ws_prog G == 
  wf_syscls G \<and> (\<forall>c\<in>set G. ws_cdecl G c) \<and> unique G"

 wf_mrT   :: "'c prog => 'c cdecl => bool"
"wf_mrT G ==
   \<lambda>(C,(D,fs,ms)).
  (C \<noteq> Object \<longrightarrow> (\<forall>(sig,rT,b)\<in>set ms. \<forall>D' rT' b'.
                      method(G,D) sig = Some(D',rT',b') --> G\<turnstile>rT\<preceq>rT'))"

 wf_cdecl_mdecl :: "'c wf_mb => 'c prog => 'c cdecl => bool"
"wf_cdecl_mdecl wf_mb G ==
   \<lambda>(C,(D,fs,ms)). (\<forall>m\<in>set ms. wf_mb G C m)"

 wf_prog :: "'c wf_mb => 'c prog => bool"
"wf_prog wf_mb G == 
     ws_prog G \<and> (\<forall>c\<in> set G. wf_mrT G c \<and> wf_cdecl_mdecl wf_mb G c)"

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

lemma wf_cdecl_mrT_cdecl_mdecl:
  "(wf_cdecl wf_mb G c) = (ws_cdecl G c \<and> wf_mrT G c \<and> wf_cdecl_mdecl wf_mb G c)"
apply (rule iffI)
apply (simp add: wf_cdecl_def ws_cdecl_def wf_mrT_def wf_cdecl_mdecl_def 
  wf_mdecl_def wf_mhead_def split_beta)+
done

lemma wf_cdecl_ws_cdecl [intro]: "wf_cdecl wf_mb G cd \<Longrightarrow> ws_cdecl G cd"
by (simp add: wf_cdecl_mrT_cdecl_mdecl)

lemma wf_prog_ws_prog [intro]: "wf_prog wf_mb G \<Longrightarrow> ws_prog G"
by (simp add: wf_prog_def ws_prog_def)

lemma wf_prog_wf_mdecl: 
  "\<lbrakk> wf_prog wf_mb G; (C,S,fs,mdecls) \<in> set G; ((mn,pTs),rT,code) \<in> set mdecls\<rbrakk>
  \<Longrightarrow> wf_mdecl wf_mb G C ((mn,pTs),rT,code)"
by (auto simp add: wf_prog_def ws_prog_def wf_mdecl_def  
  wf_cdecl_mdecl_def ws_cdecl_def)

lemma class_wf: 
 "[|class G C = Some c; wf_prog wf_mb G|] 
  ==> wf_cdecl wf_mb G (C,c) \<and> wf_mrT G (C,c)"
apply (unfold wf_prog_def ws_prog_def wf_cdecl_def class_def)
apply clarify
apply (drule_tac x="(C,c)" in bspec, fast dest: map_of_SomeD)
apply (drule_tac x="(C,c)" in bspec, fast dest: map_of_SomeD)
apply (simp add: wf_cdecl_def ws_cdecl_def wf_mdecl_def
  wf_cdecl_mdecl_def wf_mrT_def split_beta)
done

lemma class_wf_struct: 
 "[|class G C = Some c; ws_prog G|] 
  ==> ws_cdecl G (C,c)"
apply (unfold ws_prog_def class_def)
apply (fast dest: map_of_SomeD)
done

lemma class_Object [simp]: 
  "ws_prog G ==> \<exists>X fs ms. class G Object = Some (X,fs,ms)"
apply (unfold ws_prog_def wf_syscls_def class_def)
apply (auto simp: map_of_SomeI)
done

lemma class_Object_syscls [simp]: 
  "wf_syscls G ==> unique G \<Longrightarrow> \<exists>X fs ms. class G Object = Some (X,fs,ms)"
apply (unfold wf_syscls_def class_def)
apply (auto simp: map_of_SomeI)
done

lemma is_class_Object [simp]: "ws_prog G ==> is_class G Object"
apply (unfold is_class_def)
apply (simp (no_asm_simp))
done

lemma is_class_xcpt [simp]: "ws_prog G \<Longrightarrow> is_class G (Xcpt x)"
  apply (simp add: ws_prog_def wf_syscls_def)
  apply (simp add: is_class_def class_def)
  apply clarify
  apply (erule_tac x = x in allE)
  apply clarify
  apply (auto intro!: map_of_SomeI)
  done

lemma subcls1_wfD: "[|G\<turnstile>C\<prec>C1D; ws_prog G|] ==> D \<noteq> C \<and> \<not>(D,C)\<in>(subcls1 G)^+"
apply( frule r_into_trancl)
apply( drule subcls1D)
apply(clarify)
apply( drule (1) class_wf_struct)
apply( unfold ws_cdecl_def)
apply(force simp add: reflcl_trancl [THEN sym] simp del: reflcl_trancl)
done

lemma wf_cdecl_supD: 
"!!r. \<lbrakk>ws_cdecl G (C,D,r); C \<noteq> Object\<rbrakk> \<Longrightarrow> is_class G D"
apply (unfold ws_cdecl_def)
apply (auto split add: option.split_asm)
done

lemma subcls_asym: "[|ws_prog G; (C,D)\<in>(subcls1 G)^+|] ==> \<not>(D,C)\<in>(subcls1 G)^+"
apply(erule tranclE)
apply(fast dest!: subcls1_wfD )
apply(fast dest!: subcls1_wfD intro: trancl_trans)
done

lemma subcls_irrefl: "[|ws_prog G; (C,D)\<in>(subcls1 G)^+|] ==> C \<noteq> D"
apply (erule trancl_trans_induct)
apply  (auto dest: subcls1_wfD subcls_asym)
done

lemma acyclic_subcls1: "ws_prog G ==> acyclic (subcls1 G)"
apply (unfold acyclic_def)
apply (fast dest: subcls_irrefl)
done

lemma wf_subcls1: "ws_prog G ==> wf ((subcls1 G)^-1)"
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
apply (drule wf_prog_ws_prog)
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
apply( frule (1) class_wf) apply (erule conjE)+
apply (frule wf_cdecl_ws_cdecl)
apply( frule (1) wf_cdecl_supD)

apply( subgoal_tac "G\<turnstile>C\<prec>C1a")
apply( erule_tac [2] subcls1I)
apply(  rule p)
apply (unfold is_class_def)
apply auto
done
qed

lemma subcls_induct_struct: 
"[|ws_prog G; !!C. \<forall>D. (C,D)\<in>(subcls1 G)^+ --> P D ==> P C|] ==> P C"
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


lemma subcls1_induct_struct:
"[|is_class G C; ws_prog G; P Object;  
   !!C D fs ms. [|C \<noteq> Object; is_class G C; class G C = Some (D,fs,ms) \<and>  
    ws_cdecl G (C,D,fs,ms) \<and> G\<turnstile>C\<prec>C1D \<and> is_class G D \<and> P D|] ==> P C 
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
apply( rule subcls_induct_struct)
apply(  assumption)
apply( rule impI)
apply( case_tac "C = Object")
apply(  fast)
apply safe
apply( frule (1) class_wf_struct)
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

lemma field_rec: "\<lbrakk>class G C = Some (D, fs, ms); ws_prog G\<rbrakk>
\<Longrightarrow> field (G, C) =
   (if C = Object then empty else field (G, D)) ++
   map_of (map (\<lambda>(s, f). (s, C, f)) fs)"
apply (simp only: field_def)
apply (frule fields_rec, assumption)
apply (rule HOL.trans)
apply (simp add: o_def)
apply (simp (no_asm_use) 
  add: split_beta split_def o_def map_compose [THEN sym] del: map_compose)
done

lemma method_Object [simp]:
  "method (G, Object) sig = Some (D, mh, code) \<Longrightarrow> ws_prog G \<Longrightarrow> D = Object"  
  apply (frule class_Object, clarify)
  apply (drule method_rec, assumption)
  apply (auto dest: map_of_SomeD)
  done


lemma fields_Object [simp]: "\<lbrakk> ((vn, C), T) \<in> set (fields (G, Object)); ws_prog G \<rbrakk>
  \<Longrightarrow> C = Object"
apply (frule class_Object)
apply clarify
apply (subgoal_tac "fields (G, Object) = map (\<lambda>(fn,ft). ((fn,Object),ft)) fs")
apply (simp add: image_iff split_beta)
apply auto
apply (rule trans)
apply (rule fields_rec, assumption+)
apply simp
done

lemma subcls_C_Object: "[|is_class G C; ws_prog G|] ==> G\<turnstile>C\<preceq>C Object"
apply(erule subcls1_induct_struct)
apply(  assumption)
apply( fast)
apply(auto dest!: wf_cdecl_supD)
apply(erule (1) converse_rtrancl_into_rtrancl)
done

lemma is_type_rTI: "wf_mhead G sig rT ==> is_type G rT"
apply (unfold wf_mhead_def)
apply auto
done

lemma widen_fields_defpl': "[|is_class G C; ws_prog G|] ==>  
  \<forall>((fn,fd),fT)\<in>set (fields (G,C)). G\<turnstile>C\<preceq>C fd"
apply( erule subcls1_induct_struct)
apply(   assumption)
apply(  frule class_Object)
apply(  clarify)
apply(  frule fields_rec, assumption)
apply(  fastsimp)
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

lemma widen_fields_defpl: 
  "[|((fn,fd),fT) \<in> set (fields (G,C)); ws_prog G; is_class G C|] ==>  
  G\<turnstile>C\<preceq>C fd"
apply( drule (1) widen_fields_defpl')
apply (fast)
done

lemma unique_fields: 
  "[|is_class G C; ws_prog G|] ==> unique (fields (G,C))"
apply( erule subcls1_induct_struct)
apply(   assumption)
apply(  frule class_Object)
apply(  clarify)
apply(  frule fields_rec, assumption)
apply(  drule class_wf_struct, assumption)
apply(  simp add: ws_cdecl_def)
apply(  rule unique_map_inj)
apply(   simp)
apply(  rule inj_onI)
apply(  simp)
apply( safe dest!: wf_cdecl_supD)
apply( drule subcls1_wfD)
apply(  assumption)
apply( subst fields_rec)
apply   auto
apply( rotate_tac -1)
apply( frule class_wf_struct)
apply  auto
apply( simp add: ws_cdecl_def)
apply( erule unique_append)
apply(  rule unique_map_inj)
apply(   clarsimp)
apply  (rule inj_onI)
apply(  simp)
apply(auto dest!: widen_fields_defpl)
done

lemma fields_mono_lemma [rule_format (no_asm)]: 
  "[|ws_prog G; (C',C)\<in>(subcls1 G)^*|] ==>  
  x \<in> set (fields (G,C)) --> x \<in> set (fields (G,C'))"
apply(erule converse_rtrancl_induct)
apply( safe dest!: subcls1D)
apply(subst fields_rec)
apply(  auto)
done

lemma fields_mono: 
"\<lbrakk>map_of (fields (G,C)) fn = Some f; G\<turnstile>D\<preceq>C C; is_class G D; ws_prog G\<rbrakk> 
  \<Longrightarrow> map_of (fields (G,D)) fn = Some f"
apply (rule map_of_SomeI)
apply  (erule (1) unique_fields)
apply (erule (1) fields_mono_lemma)
apply (erule map_of_SomeD)
done

lemma widen_cfs_fields: 
"[|field (G,C) fn = Some (fd, fT); G\<turnstile>D\<preceq>C C; ws_prog G|]==>  
  map_of (fields (G,D)) (fn, fd) = Some fT"
apply (drule field_fields)
apply (drule rtranclD)
apply safe
apply (frule subcls_is_class)
apply (drule trancl_into_rtrancl)
apply (fast dest: fields_mono)
done

lemma method_wf_mdecl [rule_format (no_asm)]: 
  "wf_prog wf_mb G ==> is_class G C \<Longrightarrow>   
     method (G,C) sig = Some (md,mh,m) 
   --> G\<turnstile>C\<preceq>C md \<and> wf_mdecl wf_mb G md (sig,(mh,m))"
apply (frule wf_prog_ws_prog)
apply( erule subcls1_induct)
apply(   assumption)
apply(  clarify) 
apply(  frule class_Object)
apply(  clarify)
apply(  frule method_rec, assumption)
apply(  drule class_wf, assumption)
apply(  simp add: wf_cdecl_def)
apply(  drule map_of_SomeD)
apply(  subgoal_tac "md = Object")
apply(   fastsimp) 
apply(  fastsimp)
apply( clarify)
apply( frule_tac C = C in method_rec)
apply(  assumption)
apply( rotate_tac -1)
apply( simp)
apply( drule map_add_SomeD)
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


lemma method_wf_mhead [rule_format (no_asm)]: 
  "ws_prog G ==> is_class G C \<Longrightarrow>   
     method (G,C) sig = Some (md,rT,mb) 
   --> G\<turnstile>C\<preceq>C md \<and> wf_mhead G sig rT"
apply( erule subcls1_induct_struct)
apply(   assumption)
apply(  clarify) 
apply(  frule class_Object)
apply(  clarify)
apply(  frule method_rec, assumption)
apply(  drule class_wf_struct, assumption)
apply(  simp add: ws_cdecl_def)
apply(  drule map_of_SomeD)
apply(  subgoal_tac "md = Object")
apply(   fastsimp)
apply(  fastsimp)
apply( clarify)
apply( frule_tac C = C in method_rec)
apply(  assumption)
apply( rotate_tac -1)
apply( simp)
apply( drule map_add_SomeD)
apply( erule disjE)
apply(  erule_tac V = "?P --> ?Q" in thin_rl)
apply (frule map_of_SomeD)
apply (clarsimp simp add: ws_cdecl_def)
apply blast
apply clarify
apply( rule rtrancl_trans)
prefer 2
apply(  assumption)
apply( rule r_into_rtrancl)
apply( fast intro: subcls1I)
done

lemma subcls_widen_methd [rule_format (no_asm)]: 
  "[|G\<turnstile>T'\<preceq>C T; wf_prog wf_mb G|] ==>  
   \<forall>D rT b. method (G,T) sig = Some (D,rT ,b) --> 
  (\<exists>D' rT' b'. method (G,T') sig = Some (D',rT',b') \<and> G\<turnstile>D'\<preceq>C D \<and> G\<turnstile>rT'\<preceq>rT)"
apply( drule rtranclD)
apply( erule disjE)
apply(  fast)
apply( erule conjE)
apply( erule trancl_trans_induct)
prefer 2
apply(  clarify)
apply(  drule spec, drule spec, drule spec, erule (1) impE)
apply(  fast elim: widen_trans rtrancl_trans)
apply( clarify)
apply( drule subcls1D)
apply( clarify)
apply( subst method_rec)
apply(  assumption)
apply( unfold map_add_def)
apply( simp (no_asm_simp) add: wf_prog_ws_prog del: split_paired_Ex)
apply( case_tac "\<exists>z. map_of(map (\<lambda>(s,m). (s, ?C, m)) ms) sig = Some z")
apply(  erule exE)
apply(  rotate_tac -1, frule ssubst, erule_tac [2] asm_rl)
prefer 2
apply(  rotate_tac -1, frule ssubst, erule_tac [2] asm_rl)
apply(  tactic "asm_full_simp_tac (HOL_ss addsimps [not_None_eq RS sym]) 1")
apply(  simp_all (no_asm_simp) del: split_paired_Ex)
apply( frule (1) class_wf)
apply( simp (no_asm_simp) only: split_tupled_all)
apply( unfold wf_cdecl_def)
apply( drule map_of_SomeD)
apply (auto simp add: wf_mrT_def)
apply (rule rtrancl_trans)
defer
apply (rule method_wf_mhead [THEN conjunct1])
apply (simp only: wf_prog_def)
apply (simp add: is_class_def)
apply assumption
apply (auto intro: subcls1I)
done


lemma subtype_widen_methd: 
 "[| G\<turnstile> C\<preceq>C D; wf_prog wf_mb G;  
     method (G,D) sig = Some (md, rT, b) |]  
  ==> \<exists>mD' rT' b'. method (G,C) sig= Some(mD',rT',b') \<and> G\<turnstile>rT'\<preceq>rT"
apply(auto dest: subcls_widen_methd 
           simp add: wf_mdecl_def wf_mhead_def split_def)
done


lemma method_in_md [rule_format (no_asm)]: 
  "ws_prog G ==> is_class G C \<Longrightarrow> \<forall>D. method (G,C) sig = Some(D,mh,code) 
  --> is_class G D \<and> method (G,D) sig = Some(D,mh,code)"
apply (erule (1) subcls1_induct_struct)
 apply clarify
 apply (frule method_Object, assumption)
 apply hypsubst
 apply simp
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
 apply (simp add: map_add_def map_of_map split add: option.split)
done


lemma method_in_md_struct [rule_format (no_asm)]: 
  "ws_prog G ==> is_class G C \<Longrightarrow> \<forall>D. method (G,C) sig = Some(D,mh,code) 
  --> is_class G D \<and> method (G,D) sig = Some(D,mh,code)"
apply (erule (1) subcls1_induct_struct)
 apply clarify
 apply (frule method_Object, assumption)
 apply hypsubst
 apply simp
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
 apply (simp add: map_add_def map_of_map split add: option.split)
done

lemma fields_in_fd [rule_format (no_asm)]: "\<lbrakk> wf_prog wf_mb G; is_class G C\<rbrakk>
  \<Longrightarrow> \<forall> vn D T. (((vn,D),T) \<in> set (fields (G,C))
  \<longrightarrow> (is_class G D \<and> ((vn,D),T) \<in> set (fields (G,D))))"
apply (erule (1) subcls1_induct)

apply clarify
apply (frule wf_prog_ws_prog)
apply (frule fields_Object, assumption+)
apply (simp only: is_class_Object) apply simp

apply clarify
apply (frule fields_rec)
apply (simp (no_asm_simp) add: wf_prog_ws_prog)

apply (case_tac "Da=C")
apply blast			(* case Da=C *)

apply (subgoal_tac "((vn, Da), T) \<in> set (fields (G, D))") apply blast
apply (erule thin_rl)
apply (rotate_tac 1)
apply (erule thin_rl, erule thin_rl, erule thin_rl, 
      erule thin_rl, erule thin_rl, erule thin_rl)
apply auto
done

lemma field_in_fd [rule_format (no_asm)]: "\<lbrakk> wf_prog wf_mb G; is_class G C\<rbrakk>
  \<Longrightarrow> \<forall> vn D T. (field (G,C) vn = Some(D,T) 
  \<longrightarrow> is_class G D \<and> field (G,D) vn = Some(D,T))"
apply (erule (1) subcls1_induct)

apply clarify
apply (frule field_fields)
apply (drule map_of_SomeD)
apply (frule wf_prog_ws_prog)
apply (drule fields_Object, assumption+)
apply simp

apply clarify
apply (subgoal_tac "((field (G, D)) ++ map_of (map (\<lambda>(s, f). (s, C, f)) fs)) vn = Some (Da, T)")
apply (simp (no_asm_use) only: map_add_Some_iff)
apply (erule disjE)
apply (simp (no_asm_use) add: map_of_map) apply blast
apply blast
apply (rule trans [THEN sym], rule sym, assumption)
apply (rule_tac x=vn in fun_cong)
apply (rule trans, rule field_rec, assumption+)
apply (simp (no_asm_simp) add: wf_prog_ws_prog) 
apply (simp (no_asm_use)) apply blast
done


lemma widen_methd: 
"[| method (G,C) sig = Some (md,rT,b); wf_prog wf_mb G; G\<turnstile>T''\<preceq>C C|] 
  ==> \<exists>md' rT' b'. method (G,T'') sig = Some (md',rT',b') \<and> G\<turnstile>rT'\<preceq>rT"
apply( drule subcls_widen_methd)
apply   auto
done

lemma widen_field: "\<lbrakk> (field (G,C) fn) = Some (fd, fT); wf_prog wf_mb G; is_class G C \<rbrakk>
  \<Longrightarrow> G\<turnstile>C\<preceq>C fd"
apply (rule widen_fields_defpl)
apply (simp add: field_def)
apply (rule map_of_SomeD)
apply (rule table_of_remap_SomeD) 
apply assumption+
apply (simp (no_asm_simp) add: wf_prog_ws_prog)+
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

lemma fields_is_type_lemma [rule_format (no_asm)]: 
  "[|is_class G C; ws_prog G|] ==>  
  \<forall>f\<in>set (fields (G,C)). is_type G (snd f)"
apply( erule (1) subcls1_induct_struct)
apply(  frule class_Object)
apply(  clarify)
apply(  frule fields_rec, assumption)
apply(  drule class_wf_struct, assumption)
apply(  simp add: ws_cdecl_def wf_fdecl_def)
apply(  fastsimp)
apply( subst fields_rec)
apply(   fast)
apply(  assumption)
apply( clarsimp)
apply( safe)
prefer 2
apply(  force)
apply( drule (1) class_wf_struct)
apply( unfold ws_cdecl_def)
apply( clarsimp)
apply( drule (1) bspec)
apply( unfold wf_fdecl_def)
apply auto
done


lemma fields_is_type: 
  "[|map_of (fields (G,C)) fn = Some f; ws_prog G; is_class G C|] ==>  
  is_type G f"
apply(drule map_of_SomeD)
apply(drule (2) fields_is_type_lemma)
apply(auto)
done


lemma field_is_type: "\<lbrakk> ws_prog G; is_class G C; field (G, C) fn = Some (fd, fT) \<rbrakk>
  \<Longrightarrow> is_type G fT"
apply (frule_tac f="((fn, fd), fT)" in fields_is_type_lemma)
apply (auto simp add: field_def dest: map_of_SomeD)
done


lemma methd:
  "[| ws_prog G; (C,S,fs,mdecls) \<in> set G; (sig,rT,code) \<in> set mdecls |]
  ==> method (G,C) sig = Some(C,rT,code) \<and> is_class G C"
proof -
  assume wf: "ws_prog G" and C:  "(C,S,fs,mdecls) \<in> set G" and
         m: "(sig,rT,code) \<in> set mdecls"
  moreover
  from wf C have "class G C = Some (S,fs,mdecls)"
    by (auto simp add: ws_prog_def class_def is_class_def intro: map_of_SomeI)
  moreover
  from wf C 
  have "unique mdecls" by (unfold ws_prog_def ws_cdecl_def) auto
  hence "unique (map (\<lambda>(s,m). (s,C,m)) mdecls)" by (induct mdecls, auto)  
  with m 
  have "map_of (map (\<lambda>(s,m). (s,C,m)) mdecls) sig = Some (C,rT,code)"
    by (force intro: map_of_SomeI)
  ultimately
  show ?thesis by (auto simp add: is_class_def dest: method_rec)
qed


lemma wf_mb'E:
  "\<lbrakk> wf_prog wf_mb G; \<And>C S fs ms m.\<lbrakk>(C,S,fs,ms) \<in> set G; m \<in> set ms\<rbrakk> \<Longrightarrow> wf_mb' G C m \<rbrakk>
  \<Longrightarrow> wf_prog wf_mb' G"
  apply (simp only: wf_prog_def)
  apply auto
  apply (simp add: wf_cdecl_mdecl_def)
  apply safe
  apply (drule bspec, assumption) apply simp
  done


lemma fst_mono: "A \<subseteq> B \<Longrightarrow> fst ` A \<subseteq> fst ` B" by fast

lemma wf_syscls:
  "set SystemClasses \<subseteq> set G \<Longrightarrow> wf_syscls G"
  apply (drule fst_mono)
  apply (simp add: SystemClasses_def wf_syscls_def)
  apply (simp add: ObjectC_def) 
  apply (rule allI, case_tac x)
  apply (auto simp add: NullPointerC_def ClassCastC_def OutOfMemoryC_def)
  done

end
