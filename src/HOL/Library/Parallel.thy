(* Author: Florian Haftmann, TU Muenchen *)

header {* Futures and parallel lists for code generated towards Isabelle/ML *}

theory Parallel
imports Main
begin

subsection {* Futures *}

datatype 'a future = fork "unit \<Rightarrow> 'a"

primrec join :: "'a future \<Rightarrow> 'a" where
  "join (fork f) = f ()"

lemma future_eqI [intro!]:
  assumes "join f = join g"
  shows "f = g"
  using assms by (cases f, cases g) (simp add: ext)

code_type future
  (Eval "_ future")

code_const fork
  (Eval "Future.fork")

code_const join
  (Eval "Future.join")

code_reserved Eval Future future


subsection {* Parallel lists *}

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  [simp]: "map = List.map"

definition forall :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "forall = list_all"

lemma forall_all [simp]:
  "forall P xs \<longleftrightarrow> (\<forall>x\<in>set xs. P x)"
  by (simp add: forall_def list_all_iff)

definition exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "exists = list_ex"

lemma exists_ex [simp]:
  "exists P xs \<longleftrightarrow> (\<exists>x\<in>set xs. P x)"
  by (simp add: exists_def list_ex_iff)

code_const map
  (Eval "Par'_List.map")

code_const forall
  (Eval "Par'_List.forall")

code_const exists
  (Eval "Par'_List.exists")

code_reserved Eval Par_List


hide_const (open) fork join map exists forall

end

