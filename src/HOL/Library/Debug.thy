(* Author: Florian Haftmann, TU Muenchen *)

section {* Debugging facilities for code generated towards Isabelle/ML *}

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

code_printing
  constant trace \<rightharpoonup> (Eval) "Output.tracing"
| constant flush \<rightharpoonup> (Eval) "Output.tracing/ (@{make'_string} _)" -- {* note indirection via antiquotation *}
| constant timing \<rightharpoonup> (Eval) "Timing.timeap'_msg"

code_reserved Eval Output Timing

hide_const (open) trace tracing flush flushing timing

end

