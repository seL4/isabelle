(* Author: Tobias Nipkow, Daniel Stüwe *)

section {* Three-Way Comparison *}

theory Cmp
imports Main
begin

datatype cmp_val = LT | EQ | GT

function cmp :: "'a:: linorder \<Rightarrow> 'a \<Rightarrow> cmp_val" where
"x < y \<Longrightarrow> cmp x y = LT" |
"x = y \<Longrightarrow> cmp x y = EQ" |
"x > y \<Longrightarrow> cmp x y = GT"
by (auto, force)
termination by lexicographic_order

lemma 
    LT[simp]: "cmp x y = LT \<longleftrightarrow> x < y"
and EQ[simp]: "cmp x y = EQ \<longleftrightarrow> x = y"
and GT[simp]: "cmp x y = GT \<longleftrightarrow> x > y"
by (cases x y rule: linorder_cases, auto)+

lemma case_cmp_if[simp]: "(case c of EQ \<Rightarrow> e | LT \<Rightarrow> l | GT \<Rightarrow> g) =
  (if c = LT then l else if c = GT then g else e)"
by(simp split: cmp_val.split)

end
