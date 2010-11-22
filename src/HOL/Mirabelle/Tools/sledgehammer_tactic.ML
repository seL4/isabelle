(*  Title:      sledgehammer_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2010

Sledgehammer as a tactic.
*)

signature SLEDGEHAMMER_TACTICS =
sig
  val sledgehammer_with_metis_tac : Proof.context -> int -> tactic
  val sledgehammer_as_oracle_tac : Proof.context -> int -> tactic
end;

structure Sledgehammer_Tactics : SLEDGEHAMMER_TACTICS =
struct
  
fun run_atp force_full_types timeout i n ctxt goal name =
  let
    val thy = ProofContext.theory_of ctxt
    val params as {full_types, ...} =
      ((if force_full_types then [("full_types", "true")] else [])
       @ [("timeout", Int.toString (Time.toMilliseconds timeout) ^ " ms")])
(*      @ [("overlord", "true")] *)
      |> Sledgehammer_Isar.default_params thy
    val prover = Sledgehammer.get_prover_fun thy name
    val facts = []
    (* Check for constants other than the built-in HOL constants. If none of
       them appear (as should be the case for TPTP problems, unless "auto" or
       "simp" already did its "magic"), we can skip the relevance filter. *)
    val pure_goal =
      not (exists_Const (fn (s, _) => String.isSubstring "." s andalso
                                      not (String.isSubstring "HOL" s))
                        (prop_of goal))
    val problem =
      {state = Proof.init ctxt, goal = goal, subgoal = i, axioms = [],
       only = true}
  in
    prover params (K "") problem |> #message
    handle ERROR message => "Error: " ^ message ^ "\n"
  end

fun to_period ("." :: _) = []
  | to_period ("" :: ss) = to_period ss
  | to_period (s :: ss) = s :: to_period ss
  | to_period [] = []

val extract_metis_facts =
  space_explode " "
  #> fold (maps o space_explode) ["(", ")", Symbol.ENQ, Symbol.ACK, "\n"]
  #> Library.dropwhile (not o member (op =) ["metis", "metisFT"])
  #> (fn _ :: ss => SOME (to_period ss) | _ => NONE)

val atp = "e" (* or "vampire" *)

fun thms_of_name ctxt name =
  let
    val lex = Keyword.get_lexicons
    val get = maps (ProofContext.get_fact ctxt o fst)
  in
    Source.of_string name
    |> Symbol.source {do_recover=false}
    |> Token.source {do_recover=SOME false} lex Position.start
    |> Token.source_proper
    |> Source.source Token.stopper (Parse_Spec.xthms1 >> get) NONE
    |> Source.exhaust
  end

fun sledgehammer_with_metis_tac ctxt i th =
  let
    val thy = ProofContext.theory_of ctxt
    val timeout = Time.fromSeconds (60 * 60 * 24 * 365) (* one year *)
    val s = run_atp false timeout i i ctxt th atp
    val xs = these (extract_metis_facts s)
    val ths = maps (thms_of_name ctxt) xs
  in Metis_Tactics.metis_tac ctxt ths i th end

fun sledgehammer_as_oracle_tac ctxt i th =
  let
    val thy = ProofContext.theory_of ctxt
    val timeout = Time.fromSeconds (60 * 60 * 24 * 365) (* one year *)
    val s = run_atp true timeout i i ctxt th atp
  in
    if is_some (extract_metis_facts s) then Skip_Proof.cheat_tac thy th
    else Seq.empty
  end

end;
