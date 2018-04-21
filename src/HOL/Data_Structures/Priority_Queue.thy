(* Author: Tobias Nipkow, Peter Lammich *)

section \<open>Priority Queue Interface\<close>

theory Priority_Queue
imports "HOL-Library.Multiset"
begin

text \<open>Priority queue interface:\<close>
    
locale Priority_Queue =
fixes empty :: "'q"
and is_empty :: "'q \<Rightarrow> bool"
and insert :: "'a::linorder \<Rightarrow> 'q \<Rightarrow> 'q"
and get_min :: "'q \<Rightarrow> 'a"
and split_min :: "'q \<Rightarrow> 'q"
and invar :: "'q \<Rightarrow> bool"
and mset :: "'q \<Rightarrow> 'a multiset"
assumes mset_empty: "mset empty = {#}"
and is_empty: "invar q \<Longrightarrow> is_empty q = (mset q = {#})"
and mset_insert: "invar q \<Longrightarrow> mset (insert x q) = mset q + {#x#}"
and mset_split_min: "invar q \<Longrightarrow> mset q \<noteq> {#} \<Longrightarrow> 
    mset (split_min q) = mset q - {# get_min q #}"
and mset_get_min: "invar q \<Longrightarrow> mset q \<noteq> {#} \<Longrightarrow> get_min q = Min_mset (mset q)"
and invar_empty: "invar empty"
and invar_insert: "invar q \<Longrightarrow> invar (insert x q)"
and invar_split_min: "invar q \<Longrightarrow> mset q \<noteq> {#} \<Longrightarrow> invar (split_min q)"

text \<open>Extend locale with \<open>merge\<close>. Need to enforce that \<open>'q\<close> is the same in both locales.\<close>

locale Priority_Queue_Merge = Priority_Queue where empty = empty for empty :: 'q +
fixes merge :: "'q \<Rightarrow> 'q \<Rightarrow> 'q"
assumes mset_merge: "\<lbrakk> invar q1; invar q2 \<rbrakk> \<Longrightarrow> mset (merge q1 q2) = mset q1 + mset q2"
and invar_merge: "\<lbrakk> invar q1; invar q2 \<rbrakk> \<Longrightarrow> invar (merge q1 q2)"

end
