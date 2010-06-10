
(* Author: Florian Haftmann, TU Muenchen *)

header {* A huge collection of equations to generate code from *}

theory Codegenerator_Candidates
imports
  Complex_Main
  AssocList
  Binomial
  "~~/src/HOL/Decision_Procs/Commutative_Ring_Complete"
  Dlist
  Fset
  Enum
  List_Prefix
  More_List
  Nat_Infinity
  Nested_Environment
  Option_ord
  Permutation
  "~~/src/HOL/Number_Theory/Primes"
  Product_ord
  "~~/src/HOL/ex/Records"
  RBT
  SetsAndFunctions
  While_Combinator
begin

declare lexn.simps [code del]

inductive sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
    empty: "sublist [] xs"
  | drop: "sublist ys xs \<Longrightarrow> sublist ys (x # xs)"
  | take: "sublist ys xs \<Longrightarrow> sublist (x # ys) (x # xs)"

code_pred sublist .

(*avoid popular infix*)
code_reserved SML upto

end
