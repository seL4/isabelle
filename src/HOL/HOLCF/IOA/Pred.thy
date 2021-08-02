(*  Title:      HOL/HOLCF/IOA/Pred.thy
    Author:     Olaf Müller
*)

section \<open>Logical Connectives lifted to predicates\<close>

theory Pred
imports Main
begin

default_sort type

type_synonym 'a predicate = "'a \<Rightarrow> bool"

definition satisfies :: "'a \<Rightarrow> 'a predicate \<Rightarrow> bool"  ("_ \<Turnstile> _" [100, 9] 8)
  where "(s \<Turnstile> P) \<longleftrightarrow> P s"

definition valid :: "'a predicate \<Rightarrow> bool"  ("\<TTurnstile> _" [9] 8)
  where "(\<TTurnstile> P) \<longleftrightarrow> (\<forall>s. (s \<Turnstile> P))"

definition Not :: "'a predicate \<Rightarrow> 'a predicate"  ("\<^bold>\<not> _" [40] 40)
  where NOT_def: "Not P s \<longleftrightarrow> \<not> P s"

definition AND :: "'a predicate \<Rightarrow> 'a predicate \<Rightarrow> 'a predicate"  (infixr "\<^bold>\<and>" 35)
  where "(P \<^bold>\<and> Q) s \<longleftrightarrow> P s \<and> Q s"

definition OR :: "'a predicate \<Rightarrow> 'a predicate \<Rightarrow> 'a predicate"  (infixr "\<^bold>\<or>" 30)
  where "(P \<^bold>\<or> Q) s \<longleftrightarrow> P s \<or> Q s"

definition IMPLIES :: "'a predicate \<Rightarrow> 'a predicate \<Rightarrow> 'a predicate"  (infixr "\<^bold>\<longrightarrow>" 25)
  where "(P \<^bold>\<longrightarrow> Q) s \<longleftrightarrow> P s \<longrightarrow> Q s"

end
