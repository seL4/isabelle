
(* Author: Florian Haftmann, TU Muenchen *)

section {* A huge collection of equations to generate code from *}

theory Candidates
imports
  Complex_Main
  "~~/src/HOL/Library/Library"
  "~~/src/HOL/Library/Sublist_Order"
  "~~/src/HOL/Number_Theory/Eratosthenes"
  "~~/src/HOL/ex/Records"
begin

inductive sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  empty: "sublist [] xs"
| drop: "sublist ys xs \<Longrightarrow> sublist ys (x # xs)"
| take: "sublist ys xs \<Longrightarrow> sublist (x # ys) (x # xs)"

code_pred sublist .

code_reserved SML upto -- {* avoid popular infix *}

end
