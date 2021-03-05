(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_isar_preplay.ML
    Author:     Steffen Juilf Smolka, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Preplaying of Isar proofs.
*)

signature SLEDGEHAMMER_ISAR_PREPLAY =
sig
  type play_outcome = Sledgehammer_Proof_Methods.play_outcome
  type proof_method = Sledgehammer_Proof_Methods.proof_method
  type isar_step = Sledgehammer_Isar_Proof.isar_step
  type isar_proof = Sledgehammer_Isar_Proof.isar_proof
  type label = Sledgehammer_Isar_Proof.label

  val trace : bool Config.T

  type isar_preplay_data

  val peek_at_outcome : play_outcome Lazy.lazy -> play_outcome
  val enrich_context_with_local_facts : isar_proof -> Proof.context -> Proof.context
  val preplay_isar_step_for_method : Proof.context -> thm list -> Time.time -> proof_method ->
    isar_step -> play_outcome
  val preplay_isar_step : Proof.context -> thm list -> Time.time -> proof_method list ->
    isar_step -> (proof_method * play_outcome) list
  val set_preplay_outcomes_of_isar_step : Proof.context -> Time.time ->
    isar_preplay_data Unsynchronized.ref -> isar_step -> (proof_method * play_outcome) list -> unit
  val forced_intermediate_preplay_outcome_of_isar_step : isar_preplay_data -> label -> play_outcome
  val preplay_outcome_of_isar_step_for_method : isar_preplay_data -> label -> proof_method ->
    play_outcome Lazy.lazy
  val fastest_method_of_isar_step : isar_preplay_data -> label -> proof_method
  val preplay_outcome_of_isar_proof : isar_preplay_data -> isar_proof -> play_outcome
end;

structure Sledgehammer_Isar_Preplay : SLEDGEHAMMER_ISAR_PREPLAY =
struct

open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Proof_Methods
open Sledgehammer_Isar_Proof

val trace = Attrib.setup_config_bool \<^binding>\<open>sledgehammer_preplay_trace\<close> (K false)

fun peek_at_outcome outcome =
  if Lazy.is_finished outcome then Lazy.force outcome else Play_Timed_Out Time.zeroTime

fun par_list_map_filter_with_timeout _ _ _ _ [] = []
  | par_list_map_filter_with_timeout get_time min_timeout timeout0 f xs =
    let
      val next_timeout = Unsynchronized.ref timeout0

      fun apply_f x =
        let val timeout = !next_timeout in
          if timeout <= min_timeout then
            NONE
          else
            let val y = f timeout x in
              (case get_time y of
                SOME time => next_timeout := Time.min (time, !next_timeout)
              | _ => ());
              SOME y
            end
        end
    in
      chop_groups (Multithreading.max_threads ()) xs
      |> map (map_filter I o Par_List.map apply_f)
      |> flat
    end

fun enrich_context_with_local_facts proof ctxt =
  let
    val thy = Proof_Context.theory_of ctxt

    fun enrich_with_fact l t =
      Proof_Context.put_thms false (string_of_label l, SOME [Skip_Proof.make_thm thy t])

    val enrich_with_assms = fold (uncurry enrich_with_fact)

    fun enrich_with_proof (Proof {assumptions, steps = isar_steps, ...}) =
      enrich_with_assms assumptions #> fold enrich_with_step isar_steps
    and enrich_with_step (Prove {label, goal, subproofs, ...}) =
        enrich_with_fact label goal #> fold enrich_with_proof subproofs
      | enrich_with_step _ = I
  in
    enrich_with_proof proof ctxt
  end

fun preplay_trace ctxt assmsp concl outcome =
  let
    val ctxt = ctxt |> Config.put show_markup true
    val assms = op @ assmsp
    val time = Pretty.str ("[" ^ string_of_play_outcome outcome ^ "]")
    val assms = Pretty.enum " and " "using " " shows " (map (Thm.pretty_thm ctxt) assms)
    val concl = Syntax.pretty_term ctxt concl
  in
    tracing (Pretty.string_of (Pretty.blk (2, Pretty.breaks [time, assms, concl])))
  end

fun take_time timeout tac arg =
  let val timing = Timing.start () in
    (Timeout.apply timeout tac arg; Played (#cpu (Timing.result timing)))
    handle Timeout.TIMEOUT _ => Play_Timed_Out timeout
  end

fun resolve_fact_names ctxt names =
  (names
   |>> map string_of_label
   |> apply2 (maps (thms_of_name ctxt)))
  handle ERROR msg => error ("preplay error: " ^ msg)

fun thm_of_proof ctxt (Proof {fixes, assumptions, steps}) =
  let
    val thy = Proof_Context.theory_of ctxt

    val concl = 
      (case try List.last steps of
        SOME (Prove {obtains = [], goal, ...}) => goal
      | _ => raise Fail "preplay error: malformed subproof")

    val var_idx = maxidx_of_term concl + 1
    fun var_of_free (x, T) = Var ((x, var_idx), T)
    val subst = map (`var_of_free #> swap #> apfst Free) fixes
  in
    Logic.list_implies (assumptions |> map snd, concl)
    |> subst_free subst
    |> Skip_Proof.make_thm thy
  end

(* may throw exceptions *)
fun raw_preplay_step_for_method ctxt chained timeout meth
    (Prove {obtains = xs, goal, subproofs, facts, ...}) =
  let
    val goal =
      (case xs of
        [] => goal
      | _ =>
        (* proof obligation: !!thesis. (!!x1...xn. t ==> thesis) ==> thesis
           (cf. "~~/src/Pure/Isar/obtain.ML") *)
        let
          val frees = map Free xs
          val thesis =
            Free (singleton (Variable.variant_frees ctxt frees) ("thesis", HOLogic.boolT))
          val thesis_prop = HOLogic.mk_Trueprop thesis

          (* !!x1...xn. t ==> thesis *)
          val inner_prop = fold_rev Logic.all frees (Logic.mk_implies (goal, thesis_prop))
        in
          (* !!thesis. (!!x1...xn. t ==> thesis) ==> thesis *)
          Logic.all thesis (Logic.mk_implies (inner_prop, thesis_prop))
        end)

    val assmsp =
      resolve_fact_names ctxt facts
      |>> append (map (thm_of_proof ctxt) subproofs)
      |>> append chained

    fun prove () =
      Goal.prove ctxt [] [] goal (fn {context = ctxt, ...} =>
        HEADGOAL (tac_of_proof_method ctxt assmsp meth))
      handle ERROR msg => error ("Preplay error: " ^ msg)

    val play_outcome = take_time timeout prove ()
  in
    if Config.get ctxt trace then preplay_trace ctxt assmsp goal play_outcome else ();
    play_outcome
  end

fun preplay_isar_step_for_method ctxt chained timeout meth =
  try (raw_preplay_step_for_method ctxt chained timeout meth) #> the_default Play_Failed

val min_preplay_timeout = seconds 0.002

fun preplay_isar_step ctxt chained timeout0 hopeless step =
  let
    fun preplay timeout meth = (meth, preplay_isar_step_for_method ctxt chained timeout meth step)
    fun get_time (_, Played time) = SOME time
      | get_time _ = NONE

    val meths = proof_methods_of_isar_step step |> subtract (op =) hopeless
  in
    par_list_map_filter_with_timeout get_time min_preplay_timeout timeout0 preplay meths
    |> sort (play_outcome_ord o apply2 snd)
  end

type isar_preplay_data = (proof_method * play_outcome Lazy.lazy) list Canonical_Label_Tab.table

fun time_of_play (Played time) = time
  | time_of_play (Play_Timed_Out time) = time

fun add_preplay_outcomes Play_Failed _ = Play_Failed
  | add_preplay_outcomes _ Play_Failed = Play_Failed
  | add_preplay_outcomes (Played time1) (Played time2) = Played (time1 + time2)
  | add_preplay_outcomes play1 play2 =
    Play_Timed_Out (Time.+ (apply2 time_of_play (play1, play2)))

fun set_preplay_outcomes_of_isar_step ctxt timeout preplay_data
      (step as Prove {label = l, proof_methods, ...}) meths_outcomes0 =
    let
      fun lazy_preplay meth =
        Lazy.lazy (fn () => preplay_isar_step_for_method ctxt [] timeout meth step)
      val meths_outcomes = meths_outcomes0
        |> map (apsnd Lazy.value)
        |> fold (fn meth => AList.default (op =) (meth, lazy_preplay meth)) proof_methods
    in
      preplay_data := Canonical_Label_Tab.update (l, fold (AList.update (op =)) meths_outcomes [])
        (!preplay_data)
    end
  | set_preplay_outcomes_of_isar_step _ _ _ _ _ = ()

fun get_best_method_outcome force =
  tap (List.app (K () o Lazy.future Future.default_params o snd)) (* could be parallelized *)
  #> map (apsnd force)
  #> sort (play_outcome_ord o apply2 snd)
  #> hd

fun forced_intermediate_preplay_outcome_of_isar_step preplay_data l =
  let
    val meths_outcomes as (_, outcome1) :: _ = the (Canonical_Label_Tab.lookup preplay_data l)
  in
    if forall (not o Lazy.is_finished o snd) meths_outcomes then
      (case Lazy.force outcome1 of
        outcome as Played _ => outcome
      | _ => snd (get_best_method_outcome Lazy.force meths_outcomes))
    else
      let val outcome = snd (get_best_method_outcome peek_at_outcome meths_outcomes) in
        if outcome = Play_Timed_Out Time.zeroTime then
          snd (get_best_method_outcome Lazy.force meths_outcomes)
        else
          outcome
      end
  end

fun preplay_outcome_of_isar_step_for_method preplay_data l =
  AList.lookup (op =) (the (Canonical_Label_Tab.lookup preplay_data l))
  #> the_default (Lazy.value (Play_Timed_Out Time.zeroTime))

fun fastest_method_of_isar_step preplay_data =
  the o Canonical_Label_Tab.lookup preplay_data
  #> get_best_method_outcome Lazy.force
  #> fst

fun forced_outcome_of_step preplay_data (Prove {label, proof_methods, ...}) =
    Lazy.force (preplay_outcome_of_isar_step_for_method preplay_data label (hd proof_methods))
  | forced_outcome_of_step _ _ = Played Time.zeroTime

fun preplay_outcome_of_isar_proof preplay_data (Proof {steps, ...}) =
  fold_isar_steps (add_preplay_outcomes o forced_outcome_of_step preplay_data) steps
    (Played Time.zeroTime)

end;
