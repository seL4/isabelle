(*  Title:      Tools/Code/code_simp.ML
    Author:     Florian Haftmann, TU Muenchen

Connecting the simplifier and the code generator.
*)

signature CODE_SIMP =
sig
  val map_ss: (Proof.context -> Proof.context) -> theory -> theory
  val dynamic_conv: theory -> conv
  val dynamic_tac: theory -> int -> tactic
  val dynamic_value: theory -> term -> term
  val static_conv: theory -> simpset option -> string list -> conv
  val static_tac: theory -> simpset option -> string list -> Proof.context -> int -> tactic
  val setup: theory -> theory
  val trace: bool Config.T
end;

structure Code_Simp : CODE_SIMP =
struct

(* dedicated simpset *)

structure Simpset = Theory_Data
(
  type T = simpset;
  val empty = empty_ss;
  val extend = I;
  val merge = merge_ss;
);

fun map_ss f thy = Simpset.map (simpset_map (Proof_Context.init_global thy) f) thy;

fun simpset_default thy = the_default (Simpset.get thy);


(* diagnostic *)

val trace = Attrib.setup_config_bool @{binding "code_simp_trace"} (K false);

fun set_trace ctxt =
  let
    val global = Config.get ctxt trace;
  in
    ctxt |> Config.map Simplifier.simp_trace (fn b => b orelse global)
  end;


(* build simpset and conversion from program *)

fun add_stmt (Code_Thingol.Fun (_, ((_, eqs), some_cong))) ss =
      ss
      |> fold Simplifier.add_simp ((map_filter (fst o snd)) eqs)
      |> fold Simplifier.add_cong (the_list some_cong)
  | add_stmt (Code_Thingol.Classinst { inst_params, ... }) ss =
      ss
      |> fold Simplifier.add_simp (map (fst o snd) inst_params)
  | add_stmt _ ss = ss;

val add_program = Graph.fold (add_stmt o fst o snd);

fun simpset_program thy some_ss program =
  simpset_map (Proof_Context.init_global thy) (add_program program) (simpset_default thy some_ss);

fun lift_ss_conv f ss ct =  (* FIXME proper context!? *)
  f (Proof_Context.init_global (theory_of_cterm ct) |> put_simpset ss |> set_trace) ct;

fun rewrite_modulo thy some_ss program =
  lift_ss_conv Simplifier.full_rewrite (simpset_program thy some_ss program);

fun conclude_tac thy some_ss =
  let
    val ss = simpset_default thy some_ss;
  in fn ctxt => Simplifier.full_simp_tac (Simplifier.put_simpset ss ctxt) end;


(* evaluation with dynamic code context *)

fun dynamic_conv thy = Code_Thingol.dynamic_conv thy
  (fn _ => fn program => fn _ => fn _ => rewrite_modulo thy NONE program);

fun dynamic_tac thy = CONVERSION (dynamic_conv thy) THEN' conclude_tac thy NONE (Proof_Context.init_global thy);

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

fun static_tac thy some_ss consts =
  let
    val conv = static_conv thy some_ss consts;
    val tac = conclude_tac thy some_ss;
  in fn ctxt => CONVERSION conv THEN' tac ctxt end;

end;
