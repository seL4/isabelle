(* Author: Tobias Nipkow *)

section {* Three-Way Comparison *}

theory Cmp
imports Main
begin

datatype cmp = LT | EQ | GT

class cmp = linorder +
fixes cmp :: "'a \<Rightarrow> 'a \<Rightarrow> cmp"
assumes LT[simp]: "cmp x y = LT \<longleftrightarrow> x < y"
assumes EQ[simp]: "cmp x y = EQ \<longleftrightarrow> x = y"
assumes GT[simp]: "cmp x y = GT \<longleftrightarrow> x > y"

lemma case_cmp_if[simp]: "(case c of EQ \<Rightarrow> e | LT \<Rightarrow> l | GT \<Rightarrow> g) =
  (if c = LT then l else if c = GT then g else e)"
by(simp split: cmp.split)

end
