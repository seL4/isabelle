(*  Title:      ZF/AC/OrdQuant.thy
    ID:         $Id$
    Authors:    Krzysztof Grabczewski and L C Paulson

Quantifiers and union operator for ordinals. 
*)

theory OrdQuant = Ordinal:

constdefs
  
  (* Ordinal Quantifiers *)
  oall :: "[i, i => o] => o"
    "oall(A, P) == ALL x. x<A --> P(x)"
  
  oex :: "[i, i => o] => o"
    "oex(A, P)  == EX x. x<A & P(x)"

  (* Ordinal Union *)
  OUnion :: "[i, i => i] => i"
    "OUnion(i,B) == {z: UN x:i. B(x). Ord(i)}"
  
syntax
  "@oall"     :: "[idt, i, o] => o"        ("(3ALL _<_./ _)" 10)
  "@oex"      :: "[idt, i, o] => o"        ("(3EX _<_./ _)" 10)
  "@OUNION"   :: "[idt, i, i] => i"        ("(3UN _<_./ _)" 10)

translations
  "ALL x<a. P"  == "oall(a, %x. P)"
  "EX x<a. P"   == "oex(a, %x. P)"
  "UN x<a. B"   == "OUnion(a, %x. B)"

syntax (xsymbols)
  "@oall"     :: "[idt, i, o] => o"        ("(3\<forall>_<_./ _)" 10)
  "@oex"      :: "[idt, i, o] => o"        ("(3\<exists>_<_./ _)" 10)
  "@OUNION"   :: "[idt, i, i] => i"        ("(3\<Union>_<_./ _)" 10)


declare Ord_Un [intro,simp,TC]
declare Ord_UN [intro,simp,TC]
declare Ord_Union [intro,simp,TC]

(** These mostly belong to theory Ordinal **)

lemma Union_upper_le:
     "\<lbrakk>j: J;  i\<le>j;  Ord(\<Union>(J))\<rbrakk> \<Longrightarrow> i \<le> \<Union>J"
apply (subst Union_eq_UN)  
apply (rule UN_upper_le)
apply auto
done

lemma zero_not_Limit [iff]: "~ Limit(0)"
by (simp add: Limit_def)

lemma Limit_has_1: "Limit(i) \<Longrightarrow> 1 < i"
by (blast intro: Limit_has_0 Limit_has_succ)

lemma Limit_Union [rule_format]: "\<lbrakk>I \<noteq> 0;  \<forall>i\<in>I. Limit(i)\<rbrakk> \<Longrightarrow> Limit(\<Union>I)"
apply (simp add: Limit_def lt_def)
apply (blast intro!: equalityI)
done

lemma increasing_LimitI: "\<lbrakk>0<l; \<forall>x\<in>l. \<exists>y\<in>l. x<y\<rbrakk> \<Longrightarrow> Limit(l)"
apply (simp add: Limit_def lt_Ord2)
apply clarify
apply (drule_tac i=y in ltD) 
apply (blast intro: lt_trans1 succ_leI ltI lt_Ord2)
done

lemma UN_upper_lt:
     "\<lbrakk>a\<in> A;  i < b(a);  Ord(\<Union>x\<in>A. b(x))\<rbrakk> \<Longrightarrow> i < (\<Union>x\<in>A. b(x))"
by (unfold lt_def, blast) 

lemma lt_imp_0_lt: "j<i \<Longrightarrow> 0<i"
by (blast intro: lt_trans1 Ord_0_le [OF lt_Ord]) 

lemma Ord_set_cases:
   "\<forall>i\<in>I. Ord(i) \<Longrightarrow> I=0 \<or> \<Union>(I) \<in> I \<or> (\<Union>(I) \<notin> I \<and> Limit(\<Union>(I)))"
apply (clarify elim!: not_emptyE) 
apply (cases "\<Union>(I)" rule: Ord_cases) 
   apply (blast intro: Ord_Union)
  apply (blast intro: subst_elem)
 apply auto 
apply (clarify elim!: equalityE succ_subsetE)
apply (simp add: Union_subset_iff)
apply (subgoal_tac "B = succ(j)", blast )
apply (rule le_anti_sym) 
 apply (simp add: le_subset_iff) 
apply (simp add: ltI)
done

lemma Ord_Union_eq_succD: "[|\<forall>x\<in>X. Ord(x);  \<Union>X = succ(j)|] ==> succ(j) \<in> X"
by (drule Ord_set_cases, auto)

(*See also Transset_iff_Union_succ*)
lemma Ord_Union_succ_eq: "Ord(i) \<Longrightarrow> \<Union>(succ(i)) = i"
by (blast intro: Ord_trans)

lemma lt_Union_iff: "\<forall>i\<in>A. Ord(i) \<Longrightarrow> (j < \<Union>(A)) <-> (\<exists>i\<in>A. j<i)"
by (auto simp: lt_def Ord_Union)

lemma Un_upper1_lt: "[|k < i; Ord(j)|] ==> k < i Un j"
by (simp add: lt_def) 

lemma Un_upper2_lt: "[|k < j; Ord(i)|] ==> k < i Un j"
by (simp add: lt_def) 

lemma Ord_OUN [intro,simp]:
     "\<lbrakk>!!x. x<A \<Longrightarrow> Ord(B(x))\<rbrakk> \<Longrightarrow> Ord(\<Union>x<A. B(x))"
by (simp add: OUnion_def ltI Ord_UN) 

lemma OUN_upper_lt:
     "\<lbrakk>a<A;  i < b(a);  Ord(\<Union>x<A. b(x))\<rbrakk> \<Longrightarrow> i < (\<Union>x<A. b(x))"
by (unfold OUnion_def lt_def, blast )

lemma OUN_upper_le:
     "\<lbrakk>a<A;  i\<le>b(a);  Ord(\<Union>x<A. b(x))\<rbrakk> \<Longrightarrow> i \<le> (\<Union>x<A. b(x))"
apply (unfold OUnion_def)
apply auto
apply (rule UN_upper_le )
apply (auto simp add: lt_def) 
done

lemma Limit_OUN_eq: "Limit(i) ==> (UN x<i. x) = i"
by (simp add: OUnion_def Limit_Union_eq Limit_is_Ord)

(* No < version; consider (UN i:nat.i)=nat *)
lemma OUN_least:
     "(!!x. x<A ==> B(x) \<subseteq> C) ==> (UN x<A. B(x)) \<subseteq> C"
by (simp add: OUnion_def UN_least ltI)

(* No < version; consider (UN i:nat.i)=nat *)
lemma OUN_least_le:
     "[| Ord(i);  !!x. x<A ==> b(x) \<le> i |] ==> (UN x<A. b(x)) \<le> i"
by (simp add: OUnion_def UN_least_le ltI Ord_0_le)

lemma le_implies_OUN_le_OUN:
     "[| !!x. x<A ==> c(x) \<le> d(x) |] ==> (UN x<A. c(x)) \<le> (UN x<A. d(x))"
by (blast intro: OUN_least_le OUN_upper_le le_Ord2 Ord_OUN)

lemma OUN_UN_eq:
     "(!!x. x:A ==> Ord(B(x)))
      ==> (UN z < (UN x:A. B(x)). C(z)) = (UN  x:A. UN z < B(x). C(z))"
by (simp add: OUnion_def) 

lemma OUN_Union_eq:
     "(!!x. x:X ==> Ord(x))
      ==> (UN z < Union(X). C(z)) = (UN x:X. UN z < x. C(z))"
by (simp add: OUnion_def) 

end
