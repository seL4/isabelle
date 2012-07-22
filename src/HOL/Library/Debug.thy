(* Author: Florian Haftmann, TU Muenchen *)

header {* Debugging facilities for code generated towards Isabelle/ML *}

theory Debug
imports Main
begin

definition trace :: "String.literal \<Rightarrow> unit" where
  [simp]: "trace s = ()"

definition tracing :: "String.literal \<Rightarrow> 'a \<Rightarrow> 'a" where
  [simp]: "tracing s = id"

lemma [code]:
  "tracing s = (let u = trace s in id)"
  by simp

definition flush :: "'a \<Rightarrow> unit" where
  [simp]: "flush x = ()"

definition flushing :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" where
  [simp]: "flushing x = id"

lemma [code, code_unfold]:
  "flushing x = (let u = flush x in id)"
  by simp

definition timing :: "String.literal \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  [simp]: "timing s f x = f x"

code_const trace and flush and timing
  (Eval "Output.tracing" and "Output.tracing/ (PolyML.makestring _)" and "Timing.timeap'_msg")

code_reserved Eval Output PolyML Timing

hide_const (open) trace tracing flush flushing timing

end

