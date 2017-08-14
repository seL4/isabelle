(* Author: Tobias Nipkow, Peter Lammich *)

section \<open>Priority Queue Interface\<close>

theory Priority_Queue
imports "~~/src/HOL/Library/Multiset"
begin

(* FIXME abbreviation? mv *)
definition Min_mset :: "'a::linorder multiset \<Rightarrow> 'a" where
"Min_mset = Min o set_mset"

(* FIXME intros needed? *)

lemma Min_mset_contained[simp, intro]: "m\<noteq>{#} \<Longrightarrow> Min_mset m \<in># m"    
by (simp add: Min_mset_def)

lemma Min_mset_min[simp, intro]: "x\<in># m \<Longrightarrow> Min_mset m \<le> x"
by (simp add: Min_mset_def)
    
lemma Min_mset_alt: "m\<noteq>{#} \<Longrightarrow> (x=Min_mset m) \<longleftrightarrow> (x\<in>#m \<and> (\<forall>y\<in>#m. x\<le>y))"
by (simp add: antisym)    

(* FIXME a bit special *)
lemma eq_min_msetI[intro?]: 
  "m\<noteq>{#} \<Longrightarrow> (x\<in>#m \<and> (\<forall>y\<in>#m. x\<le>y)) \<Longrightarrow> x=Min_mset m"    
using Min_mset_alt by blast
    
lemma Min_mset_singleton[simp]: "Min_mset {#x#} = x"
by (simp add: Min_mset_def)
    
lemma Min_mset_insert[simp]: 
  "m\<noteq>{#} \<Longrightarrow> Min_mset (add_mset x m) = min x (Min_mset m)"
by (simp add: Min_mset_def)

text \<open>Priority queue interface:\<close>
    
locale Priority_Queue =
fixes empty :: "'q"
and is_empty :: "'q \<Rightarrow> bool"
and insert :: "'a::linorder \<Rightarrow> 'q \<Rightarrow> 'q"
and get_min :: "'q \<Rightarrow> 'a"
and del_min :: "'q \<Rightarrow> 'q"
and invar :: "'q \<Rightarrow> bool"
and mset :: "'q \<Rightarrow> 'a multiset"
assumes mset_empty: "mset empty = {#}"
and is_empty: "invar q \<Longrightarrow> is_empty q = (mset q = {#})"
and mset_insert: "invar q \<Longrightarrow> mset (insert x q) = mset q + {#x#}"
and mset_del_min: "invar q \<Longrightarrow> mset q \<noteq> {#} \<Longrightarrow> 
    mset (del_min q) = mset q - {# get_min q #}"
and mset_get_min: "invar q \<Longrightarrow> mset q \<noteq> {#} \<Longrightarrow> get_min q = Min_mset (mset q)"
and invar_empty: "invar empty"
and invar_insert: "invar q \<Longrightarrow> invar (insert x q)"
and invar_del_min: "invar q \<Longrightarrow> mset q \<noteq> {#} \<Longrightarrow> invar (del_min q)"
begin

(* FIXME why? *)

lemma get_min_alt: "invar q \<Longrightarrow> mset q \<noteq> {#} \<Longrightarrow> 
  get_min q \<in># mset q \<and> (\<forall>x\<in>#mset q. get_min q \<le> x)"
  by (simp add: mset_get_min)
  
lemmas invar_simps[simp] = invar_empty invar_insert invar_del_min
lemmas mset_simps[simp] = mset_empty is_empty mset_insert mset_del_min mset_get_min

end

end
