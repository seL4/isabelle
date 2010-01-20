(* Author: Lukas Bulwahn, TU Muenchen *)

header {* A Prototype of Quickcheck based on the Predicate Compiler *}

theory Predicate_Compile_Quickcheck
imports "../Predicate_Compile"
uses "../Tools/Predicate_Compile/predicate_compile_quickcheck.ML"
begin

setup {* Quickcheck.add_generator ("predicate_compile", Predicate_Compile_Quickcheck.quickcheck) *}
(*
datatype alphabet = a | b

inductive_set S\<^isub>1 and A\<^isub>1 and B\<^isub>1 where
  "[] \<in> S\<^isub>1"
| "w \<in> A\<^isub>1 \<Longrightarrow> b # w \<in> S\<^isub>1"
| "w \<in> B\<^isub>1 \<Longrightarrow> a # w \<in> S\<^isub>1"
| "w \<in> S\<^isub>1 \<Longrightarrow> a # w \<in> A\<^isub>1"
| "w \<in> S\<^isub>1 \<Longrightarrow> b # w \<in> S\<^isub>1"
| "\<lbrakk>v \<in> B\<^isub>1; v \<in> B\<^isub>1\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>1"

ML {* set Toplevel.debug *}

declare mem_def[code_pred_inline] Collect_def[code_pred_inline]

lemma
  "w \<in> S\<^isub>1p \<Longrightarrow> w = []"
quickcheck[generator = predicate_compile, iterations=1]
oops

theorem S\<^isub>1_sound:
"w \<in> S\<^isub>1p \<Longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[generator=predicate_compile, size=15]
oops
*)
end