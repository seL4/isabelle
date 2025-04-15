
(* Author: Florian Haftmann, TU Muenchen *)

section \<open>A huge collection of equations to generate code from\<close>

theory Candidates
imports
  Basic_Setup
  "HOL-Library.Library"
  "HOL-Library.Sorting_Algorithms"
  "HOL-Library.Subseq_Order"
  "HOL-Library.RBT"
  "HOL-Data_Structures.Tree_Map"
  "HOL-Data_Structures.Tree_Set"
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Computational_Algebra.Polynomial_Factorial"
  "HOL-Number_Theory.Eratosthenes"
  "HOL-Examples.Records"
  "HOL-Examples.Gauss_Numbers"
begin

setup \<open>Codegenerator_Test.drop_partial_term_of\<close>

text \<open>Simple example for the predicate compiler.\<close>

inductive sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  empty: "sublist [] xs"
| drop: "sublist ys xs \<Longrightarrow> sublist ys (x # xs)"
| take: "sublist ys xs \<Longrightarrow> sublist (x # ys) (x # xs)"

code_pred sublist .

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

text \<open>Explicit checks for strings etc.\<close>

definition \<open>hello = ''Hello, world!''\<close>

definition \<open>hello2 = String.explode (String.implode hello)\<close>

definition \<open>which_hello \<longleftrightarrow> hello \<le> hello2\<close>

end
