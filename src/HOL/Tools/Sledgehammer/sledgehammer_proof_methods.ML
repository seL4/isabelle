(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_proof_methods.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Reconstructors.
*)

signature SLEDGEHAMMER_PROOF_METHODS =
sig
  type stature = ATP_Problem_Generate.stature

  datatype proof_method =
    Metis_Method of string option * string option |
    Meson_Method |
    SMT2_Method |
    Blast_Method |
    Simp_Method |
    Simp_Size_Method |
    Auto_Method |
    Fastforce_Method |
    Force_Method |
    Linarith_Method |
    Presburger_Method |
    Algebra_Method

  datatype play_outcome =
    Played of Time.time |
    Play_Timed_Out of Time.time |
    Play_Failed

  type minimize_command = string list -> string
  type one_line_params =
    (proof_method * play_outcome) * string * (string * stature) list * minimize_command * int * int

  val string_of_proof_method : proof_method -> string
  val tac_of_proof_method : Proof.context -> bool -> thm list * thm list -> proof_method -> int ->
    tactic
  val string_of_play_outcome : play_outcome -> string
  val play_outcome_ord : play_outcome * play_outcome -> order
  val one_line_proof_text : int -> one_line_params -> string
end;

structure Sledgehammer_Proof_Methods : SLEDGEHAMMER_PROOF_METHODS =
struct

open ATP_Util
open ATP_Problem_Generate
open ATP_Proof_Reconstruct

datatype proof_method =
  Metis_Method of string option * string option |
  Meson_Method |
  SMT2_Method |
  Blast_Method |
  Simp_Method |
  Simp_Size_Method |
  Auto_Method |
  Fastforce_Method |
  Force_Method |
  Linarith_Method |
  Presburger_Method |
  Algebra_Method

datatype play_outcome =
  Played of Time.time |
  Play_Timed_Out of Time.time |
  Play_Failed

type minimize_command = string list -> string
type one_line_params =
  (proof_method * play_outcome) * string * (string * stature) list * minimize_command * int * int

fun string_of_proof_method meth =
  (case meth of
    Metis_Method (NONE, NONE) => "metis"
  | Metis_Method (type_enc_opt, lam_trans_opt) =>
    "metis (" ^ commas (map_filter I [type_enc_opt, lam_trans_opt]) ^ ")"
  | Meson_Method => "meson"
  | SMT2_Method => "smt2"
  | Blast_Method => "blast"
  | Simp_Method => "simp"
  | Simp_Size_Method => "simp add: size_ne_size_imp_ne"
  | Auto_Method => "auto"
  | Fastforce_Method => "fastforce"
  | Force_Method => "force"
  | Linarith_Method => "linarith"
  | Presburger_Method => "presburger"
  | Algebra_Method => "algebra")

(* Makes proof methods as silent as possible. The "set_visible" calls suppresses "Unification bound
   exceeded" warnings and the like. *)
fun silence_proof_methods debug =
  Try0.silence_methods debug
  #> Config.put SMT2_Config.verbose debug

fun tac_of_proof_method ctxt0 debug (local_facts, global_facts) meth =
  let val ctxt = silence_proof_methods debug ctxt0 in
    Method.insert_tac local_facts THEN'
    (case meth of
      Metis_Method (type_enc_opt, lam_trans_opt) =>
      Metis_Tactic.metis_tac [type_enc_opt |> the_default (hd partial_type_encs)]
        (lam_trans_opt |> the_default default_metis_lam_trans) ctxt global_facts
    | Meson_Method => Meson.meson_tac ctxt global_facts
    | SMT2_Method => SMT2_Solver.smt2_tac ctxt global_facts
    | _ =>
      Method.insert_tac global_facts THEN'
      (case meth of
        Blast_Method => blast_tac ctxt
      | Simp_Method => Simplifier.asm_full_simp_tac ctxt
      | Simp_Size_Method =>
        Simplifier.asm_full_simp_tac (Simplifier.add_simp @{thm size_ne_size_imp_ne} ctxt)
      | Auto_Method => K (Clasimp.auto_tac ctxt)
      | Fastforce_Method => Clasimp.fast_force_tac ctxt
      | Force_Method => Clasimp.force_tac ctxt
      | Linarith_Method => Lin_Arith.tac ctxt
      | Presburger_Method => Cooper.tac true [] [] ctxt
      | Algebra_Method => Groebner.algebra_tac [] [] ctxt))
  end

fun string_of_play_outcome (Played time) = string_of_ext_time (false, time)
  | string_of_play_outcome (Play_Timed_Out time) =
    if time = Time.zeroTime then "" else string_of_ext_time (true, time) ^ ", timed out"
  | string_of_play_outcome Play_Failed = "failed"

fun play_outcome_ord (Played time1, Played time2) =
    int_ord (pairself Time.toMilliseconds (time1, time2))
  | play_outcome_ord (Played _, _) = LESS
  | play_outcome_ord (_, Played _) = GREATER
  | play_outcome_ord (Play_Timed_Out time1, Play_Timed_Out time2) =
    int_ord (pairself Time.toMilliseconds (time1, time2))
  | play_outcome_ord (Play_Timed_Out _, _) = LESS
  | play_outcome_ord (_, Play_Timed_Out _) = GREATER
  | play_outcome_ord (Play_Failed, Play_Failed) = EQUAL

(* FIXME: Various bugs, esp. with "unfolding"
fun unusing_chained_facts _ 0 = ""
  | unusing_chained_facts used_chaineds num_chained =
    if length used_chaineds = num_chained then ""
    else if null used_chaineds then "(* using no facts *) "
    else "(* using only " ^ space_implode " " used_chaineds ^ " *) "
*)

fun apply_on_subgoal _ 1 = "by "
  | apply_on_subgoal 1 _ = "apply "
  | apply_on_subgoal i n =
    "prefer " ^ string_of_int i ^ " " ^ apply_on_subgoal 1 n

fun command_call name [] =
    name |> not (Symbol_Pos.is_identifier name) ? enclose "(" ")"
  | command_call name args = "(" ^ name ^ " " ^ space_implode " " args ^ ")"

(* FIXME *)
fun proof_method_command meth i n used_chaineds num_chained ss =
  (* unusing_chained_facts used_chaineds num_chained ^ *)
  apply_on_subgoal i n ^ command_call (string_of_proof_method meth) ss

fun try_command_line banner play command =
  let val s = string_of_play_outcome play in
    banner ^ ": " ^ Active.sendback_markup [Markup.padding_command] command ^
    (s |> s <> "" ? enclose " (" ")") ^ "."
  end

fun minimize_line _ [] = ""
  | minimize_line minimize_command ss =
    (case minimize_command ss of
      "" => ""
    | command => "\nTo minimize: " ^ Active.sendback_markup [Markup.padding_command] command ^ ".")

fun split_used_facts facts =
  facts
  |> List.partition (fn (_, (sc, _)) => sc = Chained)
  |> pairself (sort_distinct (string_ord o pairself fst))

fun one_line_proof_text num_chained
    ((meth, play), banner, used_facts, minimize_command, subgoal, subgoal_count) =
  let
    val (chained, extra) = split_used_facts used_facts

    val try_line =
      map fst extra
      |> proof_method_command meth subgoal subgoal_count (map fst chained) num_chained
      |> (if play = Play_Failed then enclose "One-line proof reconstruction failed: " "."
          else try_command_line banner play)
  in
    try_line ^ minimize_line minimize_command (map fst (extra @ chained))
  end

end;
