(*  Title:      Tools/Code/code_simp.ML
    Author:     Florian Haftmann, TU Muenchen

Connecting the simplifier and the code generator.
*)

signature CODE_SIMP =
sig
  val map_ss: (simpset -> simpset) -> theory -> theory
  val dynamic_eval_conv: conv
  val dynamic_eval_tac: theory -> int -> tactic
  val dynamic_eval_value: theory -> term -> term
  val static_eval_conv: theory -> simpset option -> string list -> conv
  val static_eval_tac: theory -> simpset option -> string list -> int -> tactic
  val setup: theory -> theory
end;

structure Code_Simp : CODE_SIMP =
struct

(* dedicated simpset *)

structure Simpset = Theory_Data
(
  type T = simpset;
  val empty = empty_ss;
  fun extend ss = MetaSimplifier.inherit_context empty_ss ss;
  val merge = merge_ss;
);

val map_ss = Simpset.map;

fun simpset_default thy = Simplifier.global_context thy o the_default (Simpset.get thy);


(* build simpset and conversion from program *)

fun add_stmt (Code_Thingol.Fun (_, ((_, eqs), some_cong))) ss =
      ss addsimps (map_filter (fst o snd)) eqs addcongs (the_list some_cong)
  | add_stmt (Code_Thingol.Classinst (_, (_, (classparam_instances, _)))) ss =
      ss addsimps (map (fst o snd) classparam_instances)
  | add_stmt _ ss = ss;

val add_program = Graph.fold (add_stmt o fst o snd);

fun rewrite_modulo thy some_ss program = Simplifier.full_rewrite
  (add_program program (simpset_default thy some_ss));

fun conclude_tac thy some_ss = Simplifier.full_simp_tac (simpset_default thy some_ss);


(* evaluation with dynamic code context *)

val dynamic_eval_conv = Conv.tap_thy (fn thy => Code_Thingol.dynamic_eval_conv thy
  (fn naming => fn program => fn t => fn deps => rewrite_modulo thy NONE program));

fun dynamic_eval_tac thy = CONVERSION dynamic_eval_conv THEN' conclude_tac thy NONE;

fun dynamic_eval_value thy = snd o Logic.dest_equals o Thm.prop_of o dynamic_eval_conv o Thm.cterm_of thy;

val setup = Method.setup (Binding.name "code_simp")
  (Scan.succeed (SIMPLE_METHOD' o (CHANGED_PROP oo dynamic_eval_tac o ProofContext.theory_of)))
  "simplification with code equations"
  #> Value.add_evaluator ("simp", dynamic_eval_value o ProofContext.theory_of);


(* evaluation with static code context *)

fun static_eval_conv thy some_ss consts =
  Code_Thingol.static_eval_conv_simple thy consts
    (fn program => fn thy => fn _ => fn _ => rewrite_modulo thy some_ss program);

fun static_eval_tac thy some_ss consts = CONVERSION (static_eval_conv thy some_ss consts)
  THEN' conclude_tac thy some_ss;

end;
