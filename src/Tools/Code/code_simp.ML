(*  Title:      Tools/Code/code_simp.ML
    Author:     Florian Haftmann, TU Muenchen

Connecting the simplifier and the code generator.
*)

signature CODE_SIMP =
sig
  val map_ss: (Proof.context -> Proof.context) -> theory -> theory
  val dynamic_conv: Proof.context -> conv
  val dynamic_tac: Proof.context -> int -> tactic
  val dynamic_value: Proof.context -> term -> term
  val static_conv: Proof.context -> simpset option -> string list -> Proof.context -> conv
  val static_tac: Proof.context -> simpset option -> string list -> Proof.context -> int -> tactic
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

fun simpset_default ctxt some_ss = the_default (Simpset.get (Proof_Context.theory_of ctxt)) some_ss;


(* diagnostic *)

val trace = Attrib.setup_config_bool @{binding "code_simp_trace"} (K false);

fun set_trace ctxt =
  let
    val global = Config.get ctxt trace;
  in
    ctxt |> Config.map Simplifier.simp_trace (fn b => b orelse global)
  end;


(* build simpset context and conversion from program *)

fun add_stmt (Code_Thingol.Fun ((_, eqs), some_cong)) ss =
      ss
      |> fold Simplifier.add_simp ((map_filter (fst o snd)) eqs)
      |> fold Simplifier.add_cong (the_list some_cong)
  | add_stmt (Code_Thingol.Classinst { inst_params, ... }) ss =
      ss
      |> fold Simplifier.add_simp (map (fst o snd) inst_params)
  | add_stmt _ ss = ss;

val add_program = Code_Symbol.Graph.fold (add_stmt o fst o snd);

fun simpset_program ctxt some_ss program =
  simpset_map ctxt (add_program program) (simpset_default ctxt some_ss);

fun rewrite_modulo ctxt some_ss program =
  let
    val ss = simpset_program ctxt some_ss program;
  in fn ctxt => Simplifier.full_rewrite (ctxt |> put_simpset ss |> set_trace) end;

fun conclude_tac ctxt some_ss =
  let
    val ss = simpset_default ctxt some_ss
  in fn ctxt => Simplifier.full_simp_tac (ctxt |> put_simpset ss) end;


(* evaluation with dynamic code context *)

fun dynamic_conv ctxt = Code_Thingol.dynamic_conv ctxt
  (fn program => fn _ => fn _ => fn _ => rewrite_modulo ctxt NONE program ctxt);

fun dynamic_tac ctxt = CONVERSION (dynamic_conv ctxt)
  THEN' conclude_tac ctxt NONE ctxt;

fun dynamic_value ctxt =
  snd o Logic.dest_equals o Thm.prop_of o dynamic_conv ctxt o Thm.cterm_of (Proof_Context.theory_of ctxt);

val setup =
  Method.setup @{binding code_simp}
    (Scan.succeed (SIMPLE_METHOD' o (CHANGED_PROP oo dynamic_tac)))
    "simplification with code equations"
  #> Value.add_evaluator ("simp", dynamic_value);


(* evaluation with static code context *)

fun static_conv ctxt some_ss consts =
  Code_Thingol.static_conv_simple ctxt consts
    (fn program => let val conv' = rewrite_modulo ctxt some_ss program
     in fn ctxt' => fn _ => conv' ctxt' end);

fun static_tac ctxt some_ss consts =
  let
    val conv = static_conv ctxt some_ss consts;
    val tac = conclude_tac ctxt some_ss;
  in fn ctxt' => CONVERSION (conv ctxt') THEN' (tac ctxt') end;

end;
