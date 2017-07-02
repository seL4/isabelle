
(* Author: Florian Haftmann, TU Muenchen *)

section \<open>A huge collection of equations to generate code from\<close>

theory Candidates
imports
  Complex_Main
  "~~/src/HOL/Library/Library"
  "~~/src/HOL/Library/Subseq_Order"
  "~~/src/HOL/Library/RBT"
  "~~/src/HOL/Data_Structures/Tree_Map"
  "~~/src/HOL/Data_Structures/Tree_Set"
  "~~/src/HOL/Computational_Algebra/Computational_Algebra"
  "~~/src/HOL/Computational_Algebra/Polynomial_Factorial"
  "~~/src/HOL/Number_Theory/Eratosthenes"
  "~~/src/HOL/ex/Records"
begin

text \<open>Drop technical stuff from @{theory Quickcheck_Narrowing} which is tailored towards Haskell\<close>

setup \<open>
fn thy =>
let
  val tycos = Sign.logical_types thy;
  val consts = map_filter (try (curry (Axclass.param_of_inst thy)
    @{const_name "Quickcheck_Narrowing.partial_term_of"})) tycos;
in fold Code.declare_unimplemented_global consts thy end
\<close>

text \<open>Simple example for the predicate compiler.\<close>

inductive sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  empty: "sublist [] xs"
| drop: "sublist ys xs \<Longrightarrow> sublist ys (x # xs)"
| take: "sublist ys xs \<Longrightarrow> sublist (x # ys) (x # xs)"

code_pred sublist .

text \<open>Avoid popular infix.\<close>

code_reserved SML upto

text \<open>Explicit check in \<open>OCaml\<close> for correct precedence of let expressions in list expressions\<close>

definition funny_list :: "bool list"
where
  "funny_list = [let b = True in b, False]"

definition funny_list' :: "bool list"
where
  "funny_list' = funny_list"

lemma [code]:
  "funny_list' = [True, False]"
  by (simp add: funny_list_def funny_list'_def)

definition check_list :: unit
where
  "check_list = (if funny_list = funny_list' then () else undefined)"

text \<open>Explicit check in \<open>Scala\<close> for correct bracketing of abstractions\<close>

definition funny_funs :: "(bool \<Rightarrow> bool) list \<Rightarrow> (bool \<Rightarrow> bool) list"
where
  "funny_funs fs = (\<lambda>x. x \<or> True) # (\<lambda>x. x \<or> False) # fs"

end
