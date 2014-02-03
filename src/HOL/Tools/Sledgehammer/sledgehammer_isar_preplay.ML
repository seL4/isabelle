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

  type isar_preplay_data

  val enrich_context_with_local_facts : isar_proof -> Proof.context -> Proof.context
  val preplay_isar_step : Proof.context -> Time.time -> proof_method -> isar_step -> play_outcome
  val set_preplay_outcomes_of_isar_step : Proof.context -> Time.time ->
    isar_preplay_data Unsynchronized.ref -> isar_step ->
    (proof_method * play_outcome Lazy.lazy) list -> unit
  val forced_preplay_outcome_of_isar_step : isar_preplay_data -> label -> play_outcome
  val preplay_outcome_of_isar_step_for_method : isar_preplay_data -> label -> proof_method ->
    play_outcome Lazy.lazy
  val fastest_method_of_isar_step : isar_preplay_data -> label -> proof_method
  val preplay_outcome_of_isar_proof : isar_preplay_data -> isar_proof -> play_outcome
end;

structure Sledgehammer_Isar_Preplay : SLEDGEHAMMER_ISAR_PREPLAY =
struct

open ATP_Proof_Reconstruct
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

fun preplay_trace ctxt assmsp concl outcome =
  let
    val ctxt = ctxt |> Config.put show_markup true
    val assms = op @ assmsp
    val time = Pretty.str ("[" ^ string_of_play_outcome outcome ^ "]")
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

fun tac_of_method ctxt (local_facts, global_facts) meth =
  Method.insert_tac local_facts THEN'
  (case meth of
    Meson_Method => Meson.meson_tac ctxt global_facts
  | Metis_Method (type_enc_opt, lam_trans_opt) =>
    Metis_Tactic.metis_tac [type_enc_opt |> the_default partial_type_enc]
      (the_default default_metis_lam_trans lam_trans_opt) ctxt global_facts
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
fun raw_preplay_step ctxt timeout meth (Prove (_, xs, _, t, subproofs, (fact_names, _))) =
  let
    val goal =
      (case xs of
        [] => t
      | _ =>
        (* proof obligation: !!thesis. (!!x. A x ==> thesis) ==> thesis
           (cf. "~~/src/Pure/Isar/obtain.ML") *)
        let
          (* FIXME: generate fresh name *)
          val thesis = Free ("thesis_preplay", HOLogic.boolT)
          val thesis_prop = HOLogic.mk_Trueprop thesis
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
        HEADGOAL (tac_of_method ctxt facts meth))
      handle ERROR msg => error ("Preplay error: " ^ msg)

    val play_outcome = take_time timeout prove ()
  in
    (if Config.get ctxt trace then preplay_trace ctxt facts goal play_outcome else ();
     play_outcome)
  end

fun preplay_isar_step ctxt timeout meth =
  try (raw_preplay_step ctxt timeout meth) #> the_default Play_Failed

type isar_preplay_data = (proof_method * play_outcome Lazy.lazy) list Canonical_Label_Tab.table

fun time_of_play (Played time) = time
  | time_of_play (Play_Timed_Out time) = time

fun add_preplay_outcomes Play_Failed _ = Play_Failed
  | add_preplay_outcomes _ Play_Failed = Play_Failed
  | add_preplay_outcomes (Played time1) (Played time2) = Played (Time.+ (time1, time2))
  | add_preplay_outcomes play1 play2 =
    Play_Timed_Out (Time.+ (pairself time_of_play (play1, play2)))

fun set_preplay_outcomes_of_isar_step ctxt timeout preplay_data
      (step as Prove (_, _, l, _, _, (_, meths))) meths_outcomes0 =
    let
      fun preplay meth = Lazy.lazy (fn () => preplay_isar_step ctxt timeout meth step)
      val meths_outcomes =
        fold (fn meth => AList.default (op =) (meth, preplay meth)) meths meths_outcomes0
    in
      preplay_data := Canonical_Label_Tab.map_default (l, [])
        (fold (AList.update (op =)) meths_outcomes) (!preplay_data)
    end
  | set_preplay_outcomes_of_isar_step _ _ _ _ _ = ()

fun peek_at_outcome outcome = if Lazy.is_finished outcome then Lazy.force outcome else Not_Played

(*
*)
fun forced_preplay_outcome_of_isar_step preplay_data l =
  let
    fun get_best_outcome_available get_one =
      the (Canonical_Label_Tab.lookup preplay_data l)
      |> map (apsnd get_one)
      |> sort (play_outcome_ord o pairself snd)
      |> hd |> snd
  in
    (case get_best_outcome_available peek_at_outcome of
      Not_Played => get_best_outcome_available Lazy.force
    | outcome => outcome)
  end

fun preplay_outcome_of_isar_step_for_method preplay_data l =
  the o AList.lookup (op =) (the (Canonical_Label_Tab.lookup preplay_data l))

fun fastest_method_of_isar_step preplay_data =
  the o Canonical_Label_Tab.lookup preplay_data
  #> tap (List.app (K () o Lazy.future Future.default_params o snd)) (* optional parallelism *)
  #> map (apsnd Lazy.force)
  #> sort (play_outcome_ord o pairself snd)
  #> hd #> fst

fun forced_outcome_of_step preplay_data (Prove (_, _, l, _, _, (_, meths))) =
    Lazy.force (preplay_outcome_of_isar_step_for_method preplay_data l (the_single meths))
  | forced_outcome_of_step _ _ = Played Time.zeroTime

fun preplay_outcome_of_isar_proof preplay_data (Proof (_, _, steps)) =
  fold_isar_steps (add_preplay_outcomes o forced_outcome_of_step preplay_data) steps
    (Played Time.zeroTime)

end;
