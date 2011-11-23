(*  Title:      Tools/Code/code_simp.ML
    Author:     Florian Haftmann, TU Muenchen

Connecting the simplifier and the code generator.
*)

signature CODE_SIMP =
sig
  val map_ss: (simpset -> simpset) -> theory -> theory
  val dynamic_conv: theory -> conv
  val dynamic_tac: theory -> int -> tactic
  val dynamic_value: theory -> term -> term
  val static_conv: theory -> simpset option -> string list -> conv
  val static_tac: theory -> simpset option -> string list -> int -> tactic
  val setup: theory -> theory
end;

structure Code_Simp : CODE_SIMP =
struct

(* dedicated simpset *)

structure Simpset = Theory_Data
(
  type T = simpset;
  val empty = empty_ss;
  fun extend ss = Simplifier.inherit_context empty_ss ss;
  val merge = merge_ss;
);

val map_ss = Simpset.map;

fun simpset_default thy = Simplifier.global_context thy o the_default (Simpset.get thy);


(* build simpset and conversion from program *)

fun add_stmt (Code_Thingol.Fun (_, ((_, eqs), some_cong))) ss =
      ss addsimps (map_filter (fst o snd)) eqs
      |> fold Simplifier.add_cong (the_list some_cong)
  | add_stmt (Code_Thingol.Classinst (_, (_, (classparam_instances, _)))) ss =
      ss addsimps (map (fst o snd) classparam_instances)
  | add_stmt _ ss = ss;

val add_program = Graph.fold (add_stmt o fst o snd);

fun rewrite_modulo thy some_ss program = Simplifier.full_rewrite
  (add_program program (simpset_default thy some_ss));

fun conclude_tac thy some_ss = Simplifier.full_simp_tac (simpset_default thy some_ss);


(* evaluation with dynamic code context *)

fun dynamic_conv thy = Code_Thingol.dynamic_conv thy
  (fn naming => fn program => fn t => fn deps => rewrite_modulo thy NONE program);

fun dynamic_tac thy = CONVERSION (dynamic_conv thy) THEN' conclude_tac thy NONE;

fun dynamic_value thy = snd o Logic.dest_equals o Thm.prop_of o dynamic_conv thy o Thm.cterm_of thy;

val setup =
  Method.setup @{binding code_simp}
    (Scan.succeed (SIMPLE_METHOD' o (CHANGED_PROP oo dynamic_tac o Proof_Context.theory_of)))
    "simplification with code equations"
  #> Value.add_evaluator ("simp", dynamic_value o Proof_Context.theory_of);


(* evaluation with static code context *)

fun static_conv thy some_ss consts =
  Code_Thingol.static_conv_simple thy consts
    (fn program => fn _ => fn _ => rewrite_modulo thy some_ss program);

fun static_tac thy some_ss consts = CONVERSION (static_conv thy some_ss consts)
  THEN' conclude_tac thy some_ss;

end;
