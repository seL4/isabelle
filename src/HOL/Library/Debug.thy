(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Debugging facilities for code generated towards Isabelle/ML\<close>

theory Debug
imports Main
begin

context
begin

qualified definition trace :: "String.literal \<Rightarrow> unit" where
  [simp]: "trace s = ()"

qualified definition tracing :: "String.literal \<Rightarrow> 'a \<Rightarrow> 'a" where
  [simp]: "tracing s = id"

lemma [code]:
  "tracing s = (let u = trace s in id)"
  by simp

qualified definition flush :: "'a \<Rightarrow> unit" where
  [simp]: "flush x = ()"

qualified definition flushing :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" where
  [simp]: "flushing x = id"

lemma [code, code_unfold]:
  "flushing x = (let u = flush x in id)"
  by simp

qualified definition timing :: "String.literal \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  [simp]: "timing s f x = f x"

end

code_printing
  constant Debug.trace \<rightharpoonup> (Eval) "Output.tracing"
| constant Debug.flush \<rightharpoonup> (Eval) "Output.tracing/ (@{make'_string} _)" \<comment> \<open>note indirection via antiquotation\<close>
| constant Debug.timing \<rightharpoonup> (Eval) "Timing.timeap'_msg"

code_reserved (Eval) Output Timing

end
