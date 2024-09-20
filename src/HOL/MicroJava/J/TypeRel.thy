(*  Title:      HOL/MicroJava/J/TypeRel.thy
    Author:     David von Oheimb, Technische Universitaet Muenchen
*)

section \<open>Relations between Java Types\<close>

theory TypeRel
imports Decl
begin

\<comment> \<open>direct subclass, cf. 8.1.3\<close>

inductive_set
  subcls1 :: "'c prog => (cname \<times> cname) set"
  and subcls1' :: "'c prog => cname \<Rightarrow> cname => bool" (\<open>_ \<turnstile> _ \<prec>C1 _\<close> [71,71,71] 70)
  for G :: "'c prog"
where
  "G \<turnstile> C \<prec>C1 D \<equiv> (C, D) \<in> subcls1 G"
  | subcls1I: "\<lbrakk>class G C = Some (D,rest); C \<noteq> Object\<rbrakk> \<Longrightarrow> G \<turnstile> C \<prec>C1 D"

abbreviation
  subcls  :: "'c prog => cname \<Rightarrow> cname => bool" (\<open>_ \<turnstile> _ \<preceq>C _\<close>  [71,71,71] 70)
  where "G \<turnstile> C \<preceq>C D \<equiv> (C, D) \<in> (subcls1 G)\<^sup>*"

lemma subcls1D: 
  "G\<turnstile>C\<prec>C1D \<Longrightarrow> C \<noteq> Object \<and> (\<exists>fs ms. class G C = Some (D,fs,ms))"
apply (erule subcls1.cases)
apply auto
done

lemma subcls1_def2:
  "subcls1 P =
     (SIGMA C:{C. is_class P C}. {D. C\<noteq>Object \<and> fst (the (class P C))=D})"
  by (auto simp add: is_class_def dest: subcls1D intro: subcls1I)

lemma finite_subcls1: "finite (subcls1 G)"
apply(simp add: subcls1_def2 del: mem_Sigma_iff)
apply(rule finite_SigmaI [OF finite_is_class])
apply(rule_tac B = "{fst (the (class G C))}" in finite_subset)
apply  auto
done

lemma subcls_is_class: "(C, D) \<in> (subcls1 G)\<^sup>+  \<Longrightarrow> is_class G C"
apply (unfold is_class_def)
apply(erule trancl_trans_induct)
apply (auto dest!: subcls1D)
done

lemma subcls_is_class2 [rule_format (no_asm)]: 
  "G\<turnstile>C\<preceq>C D \<Longrightarrow> is_class G D \<longrightarrow> is_class G C"
apply (unfold is_class_def)
apply (erule rtrancl_induct)
apply  (drule_tac [2] subcls1D)
apply  auto
done

definition class_rec :: "'c prog \<Rightarrow> cname \<Rightarrow> 'a \<Rightarrow>
    (cname \<Rightarrow> fdecl list \<Rightarrow> 'c mdecl list \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "class_rec G == wfrec ((subcls1 G)\<inverse>)
    (\<lambda>r C t f. case class G C of
         None \<Rightarrow> undefined
       | Some (D,fs,ms) \<Rightarrow> 
           f C fs ms (if C = Object then t else r D t f))"

lemma class_rec_lemma:
  assumes wf: "wf ((subcls1 G)\<inverse>)"
    and cls: "class G C = Some (D, fs, ms)"
  shows "class_rec G C t f = f C fs ms (if C=Object then t else class_rec G D t f)"
  by (subst wfrec_def_adm[OF class_rec_def])
     (auto simp: assms adm_wf_def fun_eq_iff subcls1I split: option.split)

definition
  "wf_class G = wf ((subcls1 G)\<inverse>)"



text \<open>Code generator setup\<close>

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  subcls1p 
  .

declare subcls1_def [code_pred_def]

code_pred 
  (modes: i \<Rightarrow> i \<times> o \<Rightarrow> bool, i \<Rightarrow> i \<times> i \<Rightarrow> bool)
  [inductify]
  subcls1 
  .

definition subcls' where "subcls' G = (subcls1p G)\<^sup>*\<^sup>*"

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  [inductify]
  subcls'
  .

lemma subcls_conv_subcls' [code_unfold]:
  "(subcls1 G)\<^sup>* = {(C, D). subcls' G C D}"
by(simp add: subcls'_def subcls1_def rtrancl_def)

lemma class_rec_code [code]:
  "class_rec G C t f = 
  (if wf_class G then 
    (case class G C of
       None \<Rightarrow> class_rec G C t f
     | Some (D, fs, ms) \<Rightarrow> 
       if C = Object then f Object fs ms t else f C fs ms (class_rec G D t f))
   else class_rec G C t f)"
apply(cases "wf_class G")
 apply(unfold class_rec_def wf_class_def)
 apply(subst wfrec, assumption)
 apply(cases "class G C")
  apply(simp add: wfrec)
 apply clarsimp
 apply(rename_tac D fs ms)
 apply(rule_tac f="f C fs ms" in arg_cong)
 apply(clarsimp simp add: cut_def)
 apply(blast intro: subcls1I)
apply simp
done

lemma wf_class_code [code]:
  "wf_class G \<longleftrightarrow> (\<forall>(C, rest) \<in> set G. C \<noteq> Object \<longrightarrow> \<not> G \<turnstile> fst (the (class G C)) \<preceq>C C)"
proof
  assume "wf_class G"
  hence wf: "wf (((subcls1 G)\<^sup>+)\<inverse>)" unfolding wf_class_def by(rule wf_converse_trancl)
  hence acyc: "acyclic ((subcls1 G)\<^sup>+)" by(auto dest: wf_acyclic)
  show "\<forall>(C, rest) \<in> set G. C \<noteq> Object \<longrightarrow> \<not> G \<turnstile> fst (the (class G C)) \<preceq>C C"
  proof(safe)
    fix C D fs ms
    assume "(C, D, fs, ms) \<in> set G"
      and "C \<noteq> Object"
      and subcls: "G \<turnstile> fst (the (class G C)) \<preceq>C C"
    from \<open>(C, D, fs, ms) \<in> set G\<close> obtain D' fs' ms'
      where "class": "class G C = Some (D', fs', ms')"
      unfolding class_def by(auto dest!: weak_map_of_SomeI)
    hence "G \<turnstile> C \<prec>C1 D'" using \<open>C \<noteq> Object\<close> ..
    hence *: "(C, D') \<in> (subcls1 G)\<^sup>+" ..
    also from * acyc have "C \<noteq> D'" by(auto simp add: acyclic_def)
    with subcls "class" have "(D', C) \<in> (subcls1 G)\<^sup>+" by(auto dest: rtranclD)
    finally show False using acyc by(auto simp add: acyclic_def)
  qed
next
  assume rhs[rule_format]: "\<forall>(C, rest) \<in> set G. C \<noteq> Object \<longrightarrow> \<not> G \<turnstile> fst (the (class G C)) \<preceq>C C"
  have "acyclic (subcls1 G)"
  proof(intro acyclicI strip notI)
    fix C
    assume "(C, C) \<in> (subcls1 G)\<^sup>+"
    thus False
    proof(cases)
      case base
      then obtain rest where "class G C = Some (C, rest)"
        and "C \<noteq> Object" by cases
      from \<open>class G C = Some (C, rest)\<close> have "(C, C, rest) \<in> set G"
        unfolding class_def by(rule map_of_SomeD)
      with \<open>C \<noteq> Object\<close> \<open>class G C = Some (C, rest)\<close>
      have "\<not> G \<turnstile> C \<preceq>C C" by(auto dest: rhs)
      thus False by simp
    next
      case (step D)
      from \<open>G \<turnstile> D \<prec>C1 C\<close> obtain rest where "class G D = Some (C, rest)"
        and "D \<noteq> Object" by cases
      from \<open>class G D = Some (C, rest)\<close> have "(D, C, rest) \<in> set G"
        unfolding class_def by(rule map_of_SomeD)
      with \<open>D \<noteq> Object\<close> \<open>class G D = Some (C, rest)\<close>
      have "\<not> G \<turnstile> C \<preceq>C D" by(auto dest: rhs)
      moreover from \<open>(C, D) \<in> (subcls1 G)\<^sup>+\<close>
      have "G \<turnstile> C \<preceq>C D" by(rule trancl_into_rtrancl)
      ultimately show False by contradiction
    qed
  qed
  thus "wf_class G" unfolding wf_class_def
    by(rule finite_acyclic_wf_converse[OF finite_subcls1])
qed

definition "method" :: "'c prog \<times> cname => (sig \<rightharpoonup> cname \<times> ty \<times> 'c)"
  \<comment> \<open>methods of a class, with inheritance, overriding and hiding, cf. 8.4.6\<close>
  where [code]: "method \<equiv> \<lambda>(G,C). class_rec G C Map.empty (\<lambda>C fs ms ts.
                           ts ++ map_of (map (\<lambda>(s,m). (s,(C,m))) ms))"

definition fields :: "'c prog \<times> cname => ((vname \<times> cname) \<times> ty) list"
  \<comment> \<open>list of fields of a class, including inherited and hidden ones\<close>
  where [code]: "fields \<equiv> \<lambda>(G,C). class_rec G C [] (\<lambda>C fs ms ts.
                           map (\<lambda>(fn,ft). ((fn,C),ft)) fs @ ts)"

definition field :: "'c prog \<times> cname => (vname \<rightharpoonup> cname \<times> ty)"
  where [code]: "field == map_of o (map (\<lambda>((fn,fd),ft). (fn,(fd,ft)))) o fields"

lemma method_rec_lemma: "[|class G C = Some (D,fs,ms); wf ((subcls1 G)\<inverse>)|] ==>
  method (G,C) = (if C = Object then Map.empty else method (G,D)) ++  
  map_of (map (\<lambda>(s,m). (s,(C,m))) ms)"
apply (unfold method_def)
apply (simp split del: if_split)
apply (erule (1) class_rec_lemma [THEN trans])
apply auto
done

lemma fields_rec_lemma: "[|class G C = Some (D,fs,ms); wf ((subcls1 G)\<inverse>)|] ==>
 fields (G,C) = 
  map (\<lambda>(fn,ft). ((fn,C),ft)) fs @ (if C = Object then [] else fields (G,D))"
apply (unfold fields_def)
apply (simp split del: if_split)
apply (erule (1) class_rec_lemma [THEN trans])
apply auto
done

lemma field_fields: 
"field (G,C) fn = Some (fd, fT) \<Longrightarrow> map_of (fields (G,C)) (fn, fd) = Some fT"
apply (unfold field_def)
apply (rule table_of_remap_SomeD)
apply simp
done


\<comment> \<open>widening, viz. method invocation conversion,cf. 5.3 i.e. sort of syntactic subtyping\<close>
inductive
  widen   :: "'c prog => [ty   , ty   ] => bool" (\<open>_ \<turnstile> _ \<preceq> _\<close>   [71,71,71] 70)
  for G :: "'c prog"
where
  refl   [intro!, simp]:       "G\<turnstile>      T \<preceq> T"   \<comment> \<open>identity conv., cf. 5.1.1\<close>
| subcls         : "G\<turnstile>C\<preceq>C D ==> G\<turnstile>Class C \<preceq> Class D"
| null   [intro!]:             "G\<turnstile>     NT \<preceq> RefT R"

code_pred widen .

lemmas refl = HOL.refl

\<comment> \<open>casting conversion, cf. 5.5 / 5.1.5\<close>
\<comment> \<open>left out casts on primitve types\<close>
inductive
  cast    :: "'c prog => [ty   , ty   ] => bool" (\<open>_ \<turnstile> _ \<preceq>? _\<close>  [71,71,71] 70)
  for G :: "'c prog"
where
  widen:  "G\<turnstile> C\<preceq> D ==> G\<turnstile>C \<preceq>? D"
| subcls: "G\<turnstile> D\<preceq>C C ==> G\<turnstile>Class C \<preceq>? Class D"

lemma widen_PrimT_RefT [iff]: "(G\<turnstile>PrimT pT\<preceq>RefT rT) = False"
apply (rule iffI)
apply (erule widen.cases)
apply auto
done

lemma widen_RefT: "G\<turnstile>RefT R\<preceq>T ==> \<exists>t. T=RefT t"
apply (ind_cases "G\<turnstile>RefT R\<preceq>T")
apply auto
done

lemma widen_RefT2: "G\<turnstile>S\<preceq>RefT R ==> \<exists>t. S=RefT t"
apply (ind_cases "G\<turnstile>S\<preceq>RefT R")
apply auto
done

lemma widen_Class: "G\<turnstile>Class C\<preceq>T ==> \<exists>D. T=Class D"
apply (ind_cases "G\<turnstile>Class C\<preceq>T")
apply auto
done

lemma widen_Class_NullT [iff]: "(G\<turnstile>Class C\<preceq>NT) = False"
apply (rule iffI)
apply (ind_cases "G\<turnstile>Class C\<preceq>NT")
apply auto
done

lemma widen_Class_Class [iff]: "(G\<turnstile>Class C\<preceq> Class D) = (G\<turnstile>C\<preceq>C D)"
apply (rule iffI)
apply (ind_cases "G\<turnstile>Class C \<preceq> Class D")
apply (auto elim: widen.subcls)
done

lemma widen_NT_Class [simp]: "G \<turnstile> T \<preceq> NT \<Longrightarrow> G \<turnstile> T \<preceq> Class D"
by (ind_cases "G \<turnstile> T \<preceq> NT",  auto)

lemma cast_PrimT_RefT [iff]: "(G\<turnstile>PrimT pT\<preceq>? RefT rT) = False"
apply (rule iffI)
apply (erule cast.cases)
apply auto
done

lemma cast_RefT: "G \<turnstile> C \<preceq>? Class D \<Longrightarrow> \<exists> rT. C = RefT rT"
apply (erule cast.cases)
apply simp apply (erule widen.cases) 
apply auto
done

theorem widen_trans[trans]: "\<lbrakk>G\<turnstile>S\<preceq>U; G\<turnstile>U\<preceq>T\<rbrakk> \<Longrightarrow> G\<turnstile>S\<preceq>T"
proof -
  assume "G\<turnstile>S\<preceq>U" thus "\<And>T. G\<turnstile>U\<preceq>T \<Longrightarrow> G\<turnstile>S\<preceq>T"
  proof induct
    case (refl T T') thus "G\<turnstile>T\<preceq>T'" .
  next
    case (subcls C D T)
    then obtain E where "T = Class E" by (blast dest: widen_Class)
    with subcls show "G\<turnstile>Class C\<preceq>T" by auto
  next
    case (null R RT)
    then obtain rt where "RT = RefT rt" by (blast dest: widen_RefT)
    thus "G\<turnstile>NT\<preceq>RT" by auto
  qed
qed

end
