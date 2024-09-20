(*  Title:      HOL/HOLCF/IOA/Pred.thy
    Author:     Olaf Müller
*)

section \<open>Logical Connectives lifted to predicates\<close>

theory Pred
imports Main
begin

default_sort type

type_synonym 'a predicate = "'a \<Rightarrow> bool"

definition satisfies :: "'a \<Rightarrow> 'a predicate \<Rightarrow> bool"  (\<open>_ \<Turnstile> _\<close> [100, 9] 8)
  where "(s \<Turnstile> P) \<longleftrightarrow> P s"

definition valid :: "'a predicate \<Rightarrow> bool"  (\<open>\<TTurnstile> _\<close> [9] 8)
  where "(\<TTurnstile> P) \<longleftrightarrow> (\<forall>s. (s \<Turnstile> P))"

definition Not :: "'a predicate \<Rightarrow> 'a predicate"  (\<open>\<^bold>\<not> _\<close> [40] 40)
  where NOT_def: "Not P s \<longleftrightarrow> \<not> P s"

definition AND :: "'a predicate \<Rightarrow> 'a predicate \<Rightarrow> 'a predicate"  (infixr \<open>\<^bold>\<and>\<close> 35)
  where "(P \<^bold>\<and> Q) s \<longleftrightarrow> P s \<and> Q s"

definition OR :: "'a predicate \<Rightarrow> 'a predicate \<Rightarrow> 'a predicate"  (infixr \<open>\<^bold>\<or>\<close> 30)
  where "(P \<^bold>\<or> Q) s \<longleftrightarrow> P s \<or> Q s"

definition IMPLIES :: "'a predicate \<Rightarrow> 'a predicate \<Rightarrow> 'a predicate"  (infixr \<open>\<^bold>\<longrightarrow>\<close> 25)
  where "(P \<^bold>\<longrightarrow> Q) s \<longleftrightarrow> P s \<longrightarrow> Q s"

end
