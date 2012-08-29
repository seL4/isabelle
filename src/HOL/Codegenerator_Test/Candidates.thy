
(* Author: Florian Haftmann, TU Muenchen *)

header {* A huge collection of equations to generate code from *}

theory Candidates
imports
  Complex_Main
  Library
  "~~/src/HOL/Library/Sublist"
  "~~/src/HOL/Number_Theory/Primes"
  "~~/src/HOL/ex/Records"
begin

inductive sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
    empty: "sublist [] xs"
  | drop: "sublist ys xs \<Longrightarrow> sublist ys (x # xs)"
  | take: "sublist ys xs \<Longrightarrow> sublist (x # ys) (x # xs)"

code_pred sublist .

(*avoid popular infix*)
code_reserved SML upto

end
