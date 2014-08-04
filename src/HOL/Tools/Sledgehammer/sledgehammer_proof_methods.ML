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
    SATx_Method |
    Blast_Method |
    Simp_Method |
    Simp_Size_Method |
    Auto_Method |
    Auto_Choice_Method |
    Force_Method |
    Linarith_Method |
    Presburger_Method |
    Algebra_Method

  datatype play_outcome =
    Played of Time.time |
    Play_Timed_Out of Time.time |
    Play_Failed

  type one_line_params =
    ((string * stature) list * (proof_method * play_outcome)) * string * int * int

  val is_proof_method_direct : proof_method -> bool
  val string_of_proof_method : Proof.context -> string list -> proof_method -> string
  val tac_of_proof_method : Proof.context -> thm list * thm list -> proof_method -> int -> tactic
  val thms_influence_proof_method : Proof.context -> proof_method -> thm list -> bool
  val string_of_play_outcome : play_outcome -> string
  val play_outcome_ord : play_outcome * play_outcome -> order
  val one_line_proof_text : Proof.context -> int -> one_line_params -> string
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
  SATx_Method |
  Blast_Method |
  Simp_Method |
  Simp_Size_Method |
  Auto_Method |
  Auto_Choice_Method |
  Force_Method |
  Linarith_Method |
  Presburger_Method |
  Algebra_Method

datatype play_outcome =
  Played of Time.time |
  Play_Timed_Out of Time.time |
  Play_Failed

type one_line_params =
  ((string * stature) list * (proof_method * play_outcome)) * string * int * int

fun is_proof_method_direct (Metis_Method _) = true
  | is_proof_method_direct Meson_Method = true
  | is_proof_method_direct SMT2_Method = true
  | is_proof_method_direct Simp_Method = true
  | is_proof_method_direct Simp_Size_Method = true
  | is_proof_method_direct _ = false

fun maybe_paren s = s |> not (Symbol_Pos.is_identifier s) ? enclose "(" ")"

fun string_of_proof_method ctxt ss meth =
  let
    val meth_s =
      (case meth of
        Metis_Method (NONE, NONE) => "metis"
      | Metis_Method (type_enc_opt, lam_trans_opt) =>
        "metis (" ^ commas (map_filter I [type_enc_opt, lam_trans_opt]) ^ ")"
      | Meson_Method => "meson"
      | SMT2_Method => "smt2"
      | SATx_Method => "satx"
      | Blast_Method => "blast"
      | Simp_Method => if null ss then "simp" else "simp add:"
      | Simp_Size_Method => "simp add: " ^ short_thm_name ctxt @{thm size_ne_size_imp_ne}
      | Auto_Method => "auto"
      | Auto_Choice_Method => "atomize_elim, auto intro!: " ^ short_thm_name ctxt @{thm choice}
      | Force_Method => "force"
      | Linarith_Method => "linarith"
      | Presburger_Method => "presburger"
      | Algebra_Method => "algebra")
  in
    maybe_paren (space_implode " " (meth_s :: ss))
  end

val silence_methods = Try0.silence_methods false

fun tac_of_proof_method ctxt (local_facts, global_facts) meth =
  Method.insert_tac local_facts THEN'
  (case meth of
    Metis_Method (type_enc_opt, lam_trans_opt) =>
    let val ctxt = Config.put Metis_Tactic.verbose false ctxt in
      Metis_Tactic.metis_tac [type_enc_opt |> the_default (hd partial_type_encs)]
        (lam_trans_opt |> the_default default_metis_lam_trans) ctxt global_facts
    end
  | Meson_Method => Meson_Tactic.meson_general_tac (silence_methods ctxt) global_facts
  | SMT2_Method =>
    let val ctxt = Config.put SMT2_Config.verbose false ctxt in
      SMT2_Solver.smt2_tac ctxt global_facts
    end
  | Simp_Method => Simplifier.asm_full_simp_tac (silence_methods ctxt addsimps global_facts)
  | Simp_Size_Method =>
    Simplifier.asm_full_simp_tac
      (silence_methods ctxt addsimps (@{thm size_ne_size_imp_ne} :: global_facts))
  | _ =>
    Method.insert_tac global_facts THEN'
    (case meth of
      SATx_Method => SAT.satx_tac ctxt
    | Blast_Method => blast_tac ctxt
    | Auto_Method => SELECT_GOAL (Clasimp.auto_tac (silence_methods ctxt))
    | Auto_Choice_Method =>
      AtomizeElim.atomize_elim_tac ctxt THEN'
      SELECT_GOAL (Clasimp.auto_tac (silence_methods ctxt addSIs @{thms choice}))
    | Force_Method => SELECT_GOAL (Clasimp.auto_tac (silence_methods ctxt))
    | Linarith_Method =>
      let val ctxt = Config.put Lin_Arith.verbose false ctxt in Lin_Arith.tac ctxt end
    | Presburger_Method => Cooper.tac true [] [] ctxt
    | Algebra_Method => Groebner.algebra_tac [] [] ctxt))

val simp_based_methods =
  [Simp_Method, Simp_Size_Method, Auto_Method, Auto_Choice_Method, Force_Method]

fun thms_influence_proof_method ctxt meth ths =
  not (member (op =) simp_based_methods meth) orelse
  let val ctxt' = silence_methods ctxt in
    (* unfortunate pointer comparison -- but it's always safe to consider a theorem useful *)
    not (pointer_eq (ctxt' addsimps ths, ctxt'))
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

fun apply_on_subgoal _ 1 = "by "
  | apply_on_subgoal 1 _ = "apply "
  | apply_on_subgoal i n = "prefer " ^ string_of_int i ^ " " ^ apply_on_subgoal 1 n

(* FIXME *)
fun proof_method_command ctxt meth i n _(*used_chaineds*) _(*num_chained*) ss =
  let val (indirect_ss, direct_ss) = if is_proof_method_direct meth then ([], ss) else (ss, []) in
    (if null indirect_ss then "" else "using " ^ space_implode " " indirect_ss ^ " ") ^
    apply_on_subgoal i n ^ string_of_proof_method ctxt direct_ss meth
  end

fun try_command_line banner play command =
  let val s = string_of_play_outcome play in
    banner ^ ": " ^ Active.sendback_markup [Markup.padding_command] command ^
    (s |> s <> "" ? enclose " (" ")") ^ "."
  end

fun one_line_proof_text ctxt num_chained
    ((used_facts, (meth, play)), banner, subgoal, subgoal_count) =
  let val (chained, extra) = List.partition (fn (_, (sc, _)) => sc = Chained) used_facts in
    map fst extra
    |> proof_method_command ctxt meth subgoal subgoal_count (map fst chained) num_chained
    |> (if play = Play_Failed then enclose "One-line proof reconstruction failed: " "."
        else try_command_line banner play)
  end

end;
