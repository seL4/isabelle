(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_proof_methods.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Reconstructors.
*)

signature SLEDGEHAMMER_PROOF_METHODS =
sig
  type stature = ATP_Problem_Generate.stature

  datatype SMT_backend =
    SMT_Z3 |
    SMT_Verit of string

  datatype proof_method =
    Metis_Method of string option * string option * string list |
    Meson_Method |
    SMT_Method of SMT_backend |
    SATx_Method |
    Argo_Method |
    Blast_Method |
    Simp_Method |
    Auto_Method |
    Fastforce_Method |
    Force_Method |
    Moura_Method |
    Linarith_Method |
    Presburger_Method |
    Algebra_Method |
    Order_Method

  datatype play_outcome =
    Played of Time.time |
    Play_Timed_Out of Time.time |
    Play_Failed

  type one_line_params =
    ((Pretty.T * stature) list * (proof_method * play_outcome)) * string * int * int

  val is_proof_method_direct : proof_method -> bool
  val pretty_proof_method : string -> string -> Pretty.T list -> proof_method -> Pretty.T
  val string_of_proof_method : string list -> proof_method -> string
  val tac_of_proof_method : Proof.context -> thm list * thm list -> proof_method -> int -> tactic
  val string_of_play_outcome : play_outcome -> string
  val play_outcome_ord : play_outcome ord
  val one_line_proof_text : Proof.context -> int -> one_line_params -> string
end;

structure Sledgehammer_Proof_Methods : SLEDGEHAMMER_PROOF_METHODS =
struct

open ATP_Util
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Sledgehammer_Util

datatype SMT_backend =
  SMT_Z3 |
  SMT_Verit of string

datatype proof_method =
  Metis_Method of string option * string option * string list |
  Meson_Method |
  SMT_Method of SMT_backend |
  SATx_Method |
  Argo_Method |
  Blast_Method |
  Simp_Method |
  Auto_Method |
  Fastforce_Method |
  Force_Method |
  Moura_Method |
  Linarith_Method |
  Presburger_Method |
  Algebra_Method |
  Order_Method

datatype play_outcome =
  Played of Time.time |
  Play_Timed_Out of Time.time |
  Play_Failed

type one_line_params =
  ((Pretty.T * stature) list * (proof_method * play_outcome)) * string * int * int

fun is_proof_method_direct (Metis_Method _) = true
  | is_proof_method_direct Meson_Method = true
  | is_proof_method_direct (SMT_Method _) = true
  | is_proof_method_direct Simp_Method = true
  | is_proof_method_direct _ = false

fun is_proof_method_multi_goal Auto_Method = true
  | is_proof_method_multi_goal _ = false

fun pretty_paren prefix suffix = Pretty.enclose (prefix ^ "(") (")" ^ suffix)
fun pretty_maybe_paren prefix suffix [pretty] =
    if Symbol_Pos.is_identifier (content_of_pretty pretty) then
      Pretty.block [Pretty.str prefix, pretty, Pretty.str suffix]
    else
      pretty_paren prefix suffix [pretty]
  | pretty_maybe_paren prefix suffix pretties = pretty_paren prefix suffix pretties

(*
Combine indexed fact names for pretty-printing.
Example: [... "assms(1)" "assms(3)" ...] becomes [... "assms(1,3)" ...]
Combines only adjacent same names.
Input should not have same name with and without index.
*)
fun merge_indexed_facts (facts: Pretty.T list) : Pretty.T list =
  let

    fun split (p: Pretty.T) : (string * string) option =
      try (unsuffix ")" o content_of_pretty) p
      |> Option.mapPartial (first_field "(")

    fun add_pretty (name,is) = (SOME (name,is),Pretty.str (name ^ "(" ^ is ^ ")"))

    fun merge ((SOME (name1,is1),p1) :: (y as (SOME (name2,is2),_)) :: zs) =
        if name1 = name2
        then merge (add_pretty (name1,is1 ^ "," ^ is2) :: zs)
        else p1 :: merge (y :: zs)
      | merge ((_,p) :: ys) = p :: merge ys
      | merge [] = []

  in
    merge (map (`split) facts)
  end

fun pretty_proof_method prefix suffix facts meth =
  let
    val meth_s =
      (case meth of
        Metis_Method (NONE, NONE, additional_fact_names) =>
        implode_space ("metis" :: additional_fact_names)
      | Metis_Method (type_enc_opt, lam_trans_opt, additional_fact_names) =>
        implode_space ("metis" ::
          "(" ^ commas (map_filter I [type_enc_opt, lam_trans_opt]) ^ ")" ::
          additional_fact_names)
      | Meson_Method => "meson"
      | SMT_Method SMT_Z3 => "smt (z3)"
      | SMT_Method (SMT_Verit strategy) =>
        "smt (" ^ commas ("verit" :: (if strategy = "default" then [] else [strategy])) ^ ")"
      | SATx_Method => "satx"
      | Argo_Method => "argo"
      | Blast_Method => "blast"
      | Simp_Method => if null facts then "simp" else "simp add:"
      | Auto_Method => "auto"
      | Fastforce_Method => "fastforce"
      | Force_Method => "force"
      | Moura_Method => "moura"
      | Linarith_Method => "linarith"
      | Presburger_Method => "presburger"
      | Algebra_Method => "algebra"
      | Order_Method => "order")
  in
    pretty_maybe_paren prefix suffix
      (Pretty.str meth_s :: merge_indexed_facts facts |> Pretty.breaks)
  end

fun string_of_proof_method ss =
  pretty_proof_method "" "" (map Pretty.str ss)
  #> content_of_pretty

fun tac_of_proof_method ctxt (local_facts, global_facts) meth =
  let
    fun tac_of_metis (type_enc_opt, lam_trans_opt, additional_fact_names) =
      let
        val additional_facts = maps (thms_of_name ctxt) additional_fact_names
        val ctxt = ctxt
          |> Config.put Metis_Tactic.verbose false
          |> Config.put Metis_Tactic.trace false
      in
        SELECT_GOAL (Metis_Tactic.metis_method ((Option.map single type_enc_opt, lam_trans_opt),
          additional_facts @ global_facts) ctxt local_facts)
      end

    fun tac_of_smt SMT_Z3 = SMT_Solver.smt_tac
      | tac_of_smt (SMT_Verit strategy) = Verit_Strategies.verit_tac_stgy strategy
  in
    (case meth of
      Metis_Method options => tac_of_metis options
    | SMT_Method backend => tac_of_smt backend ctxt (local_facts @ global_facts)
    | _ =>
      Method.insert_tac ctxt local_facts THEN'
      (case meth of
        Meson_Method => Meson_Tactic.meson_general_tac ctxt global_facts
      | Simp_Method => Simplifier.asm_full_simp_tac (ctxt addsimps global_facts)
      | _ =>
        Method.insert_tac ctxt global_facts THEN'
        (case meth of
          SATx_Method => SAT.satx_tac ctxt
        | Argo_Method => Argo_Tactic.argo_tac ctxt []
        | Blast_Method => blast_tac ctxt
        | Auto_Method => SELECT_GOAL (Clasimp.auto_tac ctxt)
        | Fastforce_Method => Clasimp.fast_force_tac ctxt
        | Force_Method => Clasimp.force_tac ctxt
        | Moura_Method => moura_tac ctxt
        | Linarith_Method => Lin_Arith.tac ctxt
        | Presburger_Method => Cooper.tac true [] [] ctxt
        | Algebra_Method => Groebner.algebra_tac [] [] ctxt
        | Order_Method => HOL_Order_Tac.tac [] ctxt)))
  end

fun string_of_play_outcome (Played time) = string_of_ext_time (false, time)
  | string_of_play_outcome (Play_Timed_Out time) =
    if time = Time.zeroTime then "" else string_of_ext_time (true, time) ^ ", timed out"
  | string_of_play_outcome Play_Failed = "failed"

fun play_outcome_ord (Played time1, Played time2) = Time.compare (time1, time2)
  | play_outcome_ord (Played _, _) = LESS
  | play_outcome_ord (_, Played _) = GREATER
  | play_outcome_ord (Play_Timed_Out time1, Play_Timed_Out time2) = Time.compare (time1, time2)
  | play_outcome_ord (Play_Timed_Out _, _) = LESS
  | play_outcome_ord (_, Play_Timed_Out _) = GREATER
  | play_outcome_ord (Play_Failed, Play_Failed) = EQUAL

fun apply_on_subgoal _ 1 = "by "
  | apply_on_subgoal 1 _ = "apply "
  | apply_on_subgoal i n = "prefer " ^ string_of_int i ^ " " ^ apply_on_subgoal 1 n

(* FIXME *)
fun proof_method_command meth i n used_chaineds _(*num_chained*) extras =
  let
    val (indirect_facts, direct_facts) =
      if is_proof_method_direct meth then ([], extras) else (extras, [])
    val suffix =
      if is_proof_method_multi_goal meth andalso n <> 1 then "[1]" else ""
  in
    (if null indirect_facts then []
     else Pretty.str "using" :: merge_indexed_facts indirect_facts) @
    [pretty_proof_method (apply_on_subgoal i n) suffix direct_facts meth]
    |> Pretty.block o Pretty.breaks
    |> Pretty.symbolic_string_of (* markup string *)
  end

fun try_command_line banner play command =
  let val s = string_of_play_outcome play in
    (* Add optional markup break (command may need multiple lines) *)
    banner ^ Markup.markup (Markup.break {width = 1, indent = 2}) " " ^
    Active.sendback_markup_command command ^ (s |> s <> "" ? enclose " (" ")")
  end

val failed_command_line =
  prefix ("One-line proof reconstruction failed:" ^
    (* Add optional markup break (command may need multiple lines) *)
    Markup.markup (Markup.break {width = 1, indent = 2}) " ")

fun one_line_proof_text _ num_chained
    ((used_facts, (meth, play)), banner, subgoal, subgoal_count) =
  let val (chained, extra) = List.partition (fn (_, (sc, _)) => sc = Chained) used_facts in
    map fst extra
    |> proof_method_command meth subgoal subgoal_count (map fst chained) num_chained
    |> (if play = Play_Failed then failed_command_line else try_command_line banner play)
  end

end;
