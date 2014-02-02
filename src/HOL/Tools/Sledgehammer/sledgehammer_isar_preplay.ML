(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_isar_preplay.ML
    Author:     Steffen Juilf Smolka, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Preplaying of Isar proofs.
*)

signature SLEDGEHAMMER_ISAR_PREPLAY =
sig
  type play_outcome = Sledgehammer_Reconstructor.play_outcome
  type proof_method = Sledgehammer_Isar_Proof.proof_method
  type isar_step = Sledgehammer_Isar_Proof.isar_step
  type isar_proof = Sledgehammer_Isar_Proof.isar_proof
  type label = Sledgehammer_Isar_Proof.label

  val trace : bool Config.T

  type isar_preplay_data =
    {preplay_step: Time.time -> proof_method -> isar_step -> play_outcome,
     set_preplay_outcomes: label -> (proof_method * play_outcome Lazy.lazy) list -> unit,
     preplay_outcome: label -> proof_method -> play_outcome Lazy.lazy,
     overall_preplay_outcome: isar_proof -> play_outcome}

  val enrich_context_with_local_facts : isar_proof -> Proof.context -> Proof.context
  val preplay_data_of_isar_proof : Proof.context -> string -> string -> Time.time -> isar_proof ->
    isar_preplay_data
end;

structure Sledgehammer_Isar_Preplay : SLEDGEHAMMER_ISAR_PREPLAY =
struct

open Sledgehammer_Util
open Sledgehammer_Reconstructor
open Sledgehammer_Isar_Proof

val trace = Attrib.setup_config_bool @{binding sledgehammer_preplay_trace} (K false)

fun enrich_context_with_local_facts proof ctxt =
  let
    val thy = Proof_Context.theory_of ctxt

    fun enrich_with_fact l t =
      Proof_Context.put_thms false (string_of_label l, SOME [Skip_Proof.make_thm thy t])

    val enrich_with_assms = fold (uncurry enrich_with_fact)

    fun enrich_with_proof (Proof (_, assms, isar_steps)) =
      enrich_with_assms assms #> fold enrich_with_step isar_steps
    and enrich_with_step (Let _) = I
      | enrich_with_step (Prove (_, _, l, t, subproofs, _)) =
        enrich_with_fact l t #> fold enrich_with_proof subproofs
  in
    enrich_with_proof proof ctxt
  end

fun preplay_trace ctxt assmsp concl result =
  let
    val ctxt = ctxt |> Config.put show_markup true
    val assms = op @ assmsp
    val time = Pretty.str ("[" ^ string_of_play_outcome result ^ "]")
    val assms = Pretty.enum " and " "using " " shows " (map (Display.pretty_thm ctxt) assms)
    val concl = Syntax.pretty_term ctxt concl
  in
    tracing (Pretty.string_of (Pretty.blk (2, Pretty.breaks [time, assms, concl])))
  end

fun take_time timeout tac arg =
  let val timing = Timing.start () in
    (TimeLimit.timeLimit timeout tac arg; Played (#cpu (Timing.result timing)))
    handle TimeLimit.TimeOut => Play_Timed_Out timeout
  end

fun resolve_fact_names ctxt names =
  (names
   |>> map string_of_label
   |> pairself (maps (thms_of_name ctxt)))
  handle ERROR msg => error ("preplay error: " ^ msg)

fun thm_of_proof ctxt (Proof (fixed_frees, assms, steps)) =
  let
    val thy = Proof_Context.theory_of ctxt

    val concl = 
      (case try List.last steps of
        SOME (Prove (_, [], _, t, _, _)) => t
      | _ => raise Fail "preplay error: malformed subproof")

    val var_idx = maxidx_of_term concl + 1
    fun var_of_free (x, T) = Var ((x, var_idx), T)
    val subst = map (`var_of_free #> swap #> apfst Free) fixed_frees
  in
    Logic.list_implies (assms |> map snd, concl)
    |> subst_free subst
    |> Skip_Proof.make_thm thy
  end

fun tac_of_method meth type_enc lam_trans ctxt (local_facts, global_facts) =
  Method.insert_tac local_facts THEN'
  (case meth of
    Meson_Method => Meson.meson_tac ctxt global_facts
  | Metis_Method => Metis_Tactic.metis_tac [type_enc] lam_trans ctxt global_facts
  | _ =>
    Method.insert_tac global_facts THEN'
    (case meth of
      Simp_Method => Simplifier.asm_full_simp_tac ctxt
    | Simp_Size_Method =>
      Simplifier.asm_full_simp_tac (Simplifier.add_simp @{thm size_ne_size_imp_ne} ctxt)
    | Auto_Method => K (Clasimp.auto_tac ctxt)
    | Fastforce_Method => Clasimp.fast_force_tac ctxt
    | Force_Method => Clasimp.force_tac ctxt
    | Arith_Method => Arith_Data.arith_tac ctxt
    | Blast_Method => blast_tac ctxt
    | Algebra_Method => Groebner.algebra_tac [] [] ctxt
    | _ => raise Fail "Sledgehammer_Isar_Preplay: tac_of_method"))

(* main function for preplaying Isar steps; may throw exceptions *)
fun raw_preplay_step type_enc lam_trans ctxt timeout meth
      (Prove (_, xs, _, t, subproofs, (fact_names, _))) =
    let
      val goal =
        (case xs of
          [] => t
        | _ =>
          (* proof obligation: !!thesis. (!!x. A x ==> thesis) ==> thesis
             (cf. "~~/src/Pure/Isar/obtain.ML") *)
          let
            (* FIXME: generate fresh name *)
            val thesis = Free ("thesis", HOLogic.boolT)
            val thesis_prop = thesis |> HOLogic.mk_Trueprop
            val frees = map Free xs

            (* !!x1..xn. t ==> thesis (xs = [x1, .., xn]) *)
            val inner_prop = fold_rev Logic.all frees (Logic.mk_implies (t, thesis_prop))
          in
            (* !!thesis. (!!x1..xn. t ==> thesis) ==> thesis *)
            Logic.all thesis (Logic.mk_implies (inner_prop, thesis_prop))
          end)

      val facts =
        resolve_fact_names ctxt fact_names
        |>> append (map (thm_of_proof ctxt) subproofs)

      fun prove () =
        Goal.prove ctxt [] [] goal (fn {context = ctxt, ...} =>
          HEADGOAL (tac_of_method meth type_enc lam_trans ctxt facts))
        handle ERROR msg => error ("Preplay error: " ^ msg)

      val play_outcome = take_time timeout prove ()
    in
      (if Config.get ctxt trace then preplay_trace ctxt facts goal play_outcome else ();
       play_outcome)
    end

type isar_preplay_data =
  {set_preplay_outcomes: label -> (proof_method * play_outcome Lazy.lazy) list -> unit,
   preplay_outcome: label -> proof_method -> play_outcome Lazy.lazy,
   preplay_step: Time.time -> proof_method -> isar_step -> play_outcome,
   overall_preplay_outcome: isar_proof -> play_outcome}

fun time_of_play (Played time) = time
  | time_of_play (Play_Timed_Out time) = time

fun merge_preplay_outcomes Play_Failed _ = Play_Failed
  | merge_preplay_outcomes _ Play_Failed = Play_Failed
  | merge_preplay_outcomes (Played time1) (Played time2) = Played (Time.+ (time1, time2))
  | merge_preplay_outcomes play1 play2 =
    Play_Timed_Out (Time.+ (pairself time_of_play (play1, play2)))

(* Given a (canonically labeled) proof, produces an imperative preplay interface with a shared table
   mapping from labels to preplay results. The preplay results are caluclated lazily and cached to
   avoid repeated calculation. *)
fun preplay_data_of_isar_proof ctxt type_enc lam_trans preplay_timeout proof =
  let
    fun preplay_step timeout meth =
      try (raw_preplay_step type_enc lam_trans ctxt timeout meth)
      #> the_default Play_Failed

    val preplay_tab = Unsynchronized.ref Canonical_Label_Tab.empty

    fun set_preplay_outcomes l meths_outcomes =
      preplay_tab := Canonical_Label_Tab.map_entry l (fold (AList.update (op =)) meths_outcomes)
        (!preplay_tab)

    fun preplay_outcome l meth =
      (case Canonical_Label_Tab.lookup (!preplay_tab) l of
        SOME meths_outcomes =>
        (case AList.lookup (op =) meths_outcomes meth of
          SOME outcome => outcome
        | NONE => raise Fail "Sledgehammer_Isar_Preplay: missing method")
      | NONE => raise Fail "Sledgehammer_Isar_Preplay: missing label")

    fun result_of_step (Prove (_, _, l, _, _, (_, meth :: _))) =
        Lazy.force (preplay_outcome l meth)
      | result_of_step _ = Played Time.zeroTime

    fun overall_preplay_outcome (Proof (_, _, steps)) =
      fold_isar_steps (merge_preplay_outcomes o result_of_step) steps (Played Time.zeroTime)

    fun reset_preplay_outcomes (step as Prove (_, _, l, _, _, (_, meths))) =
        preplay_tab := Canonical_Label_Tab.update (l, map (fn meth =>
            (meth, Lazy.lazy (fn () => preplay_step preplay_timeout meth step))) meths)
          (!preplay_tab)
      | reset_preplay_outcomes _ = ()

    val _ = fold_isar_steps (K o reset_preplay_outcomes) (steps_of_proof proof) ()
  in
    {preplay_step = preplay_step,
     set_preplay_outcomes = set_preplay_outcomes,
     preplay_outcome = preplay_outcome,
     overall_preplay_outcome = overall_preplay_outcome}
  end

end;
