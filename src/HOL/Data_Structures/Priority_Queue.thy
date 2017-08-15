(* Author: Tobias Nipkow, Peter Lammich *)

section \<open>Priority Queue Interface\<close>

theory Priority_Queue
imports "~~/src/HOL/Library/Multiset"
begin

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
