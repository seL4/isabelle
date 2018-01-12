(* Author: Tobias Nipkow, Daniel Stüwe *)

section \<open>Three-Way Comparison\<close>

theory Cmp
imports Main
begin

datatype cmp_val = LT | EQ | GT

definition cmp :: "'a:: linorder \<Rightarrow> 'a \<Rightarrow> cmp_val" where
"cmp x y = (if x < y then LT else if x=y then EQ else GT)"

lemma 
    LT[simp]: "cmp x y = LT \<longleftrightarrow> x < y"
and EQ[simp]: "cmp x y = EQ \<longleftrightarrow> x = y"
and GT[simp]: "cmp x y = GT \<longleftrightarrow> x > y"
by (auto simp: cmp_def)

lemma case_cmp_if[simp]: "(case c of EQ \<Rightarrow> e | LT \<Rightarrow> l | GT \<Rightarrow> g) =
  (if c = LT then l else if c = GT then g else e)"
by(simp split: cmp_val.split)

end
