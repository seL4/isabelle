(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_preplay.ML
    Author:     Steffen Juilf Smolka, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Preplaying of Isar proofs.
*)

signature SLEDGEHAMMER_PREPLAY =
sig
  type play_outcome = Sledgehammer_Reconstructor.play_outcome
  type isar_proof = Sledgehammer_Proof.isar_proof
  type isar_step = Sledgehammer_Proof.isar_step
  type label = Sledgehammer_Proof.label

  val trace: bool Config.T

  type preplay_interface =
    {get_preplay_outcome: label -> play_outcome,
     set_preplay_outcome: label -> play_outcome -> unit,
     preplay_quietly: Time.time -> isar_step -> play_outcome,
     overall_preplay_outcome: isar_proof -> play_outcome}

  val proof_preplay_interface: bool -> Proof.context -> string -> string -> bool -> Time.time ->
    isar_proof -> preplay_interface
end;

structure Sledgehammer_Preplay : SLEDGEHAMMER_PREPLAY =
struct

open ATP_Util
open Sledgehammer_Util
open Sledgehammer_Reconstructor
open Sledgehammer_Proof

val trace = Attrib.setup_config_bool @{binding sledgehammer_preplay_trace} (K false)

fun preplay_trace ctxt assms concl result =
  let
    val ctxt = ctxt |> Config.put show_markup true
    val time = "[" ^ string_of_play_outcome result ^ "]" |> Pretty.str
    val nr_of_assms = length assms
    val assms = assms
      |> map (Display.pretty_thm ctxt)
      |> (fn [] => Pretty.str ""
           | [a] => a
           | assms => Pretty.enum ";" "\<lbrakk>" "\<rbrakk>" assms)  (* Syntax.pretty_term!? *)
    val concl = concl |> Syntax.pretty_term ctxt
    val trace_list = []
      |> cons concl
      |> nr_of_assms > 0 ? cons (Pretty.str "\<Longrightarrow>")
      |> cons assms
      |> cons time
    val pretty_trace = Pretty.blk (2, Pretty.breaks trace_list)
  in
    tracing (Pretty.string_of pretty_trace)
  end

fun take_time timeout tac arg =
  let val timing = Timing.start () in
    (TimeLimit.timeLimit timeout tac arg; Played (#cpu (Timing.result timing)))
    handle TimeLimit.TimeOut => Play_Timed_Out timeout
  end

fun resolve_fact_names ctxt names =
  (names
   |>> map string_of_label
   |> op @
   |> maps (thms_of_name ctxt))
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

fun tac_of_method meth type_enc lam_trans ctxt facts =
  (case meth of
    Metis_Method => Metis_Tactic.metis_tac [type_enc] lam_trans ctxt facts
  | Meson_Method => Meson.meson_tac ctxt facts
  | _ =>
    Method.insert_tac facts THEN'
    (case meth of
      Metis_New_Skolem_Method => Metis_Tactic.metis_tac [type_enc] lam_trans ctxt []
    | Simp_Method => Simplifier.asm_full_simp_tac ctxt
    | Simp_Size_Method =>
      Simplifier.asm_full_simp_tac (Simplifier.add_simp @{thm size_ne_size_imp_ne} ctxt)
    | Auto_Method => K (Clasimp.auto_tac ctxt)
    | Fastforce_Method => Clasimp.fast_force_tac ctxt
    | Force_Method => Clasimp.force_tac ctxt
    | Arith_Method => Arith_Data.arith_tac ctxt
    | Blast_Method => blast_tac ctxt
    | _ => raise Fail "Sledgehammer_Preplay: tac_of_method"))

(* main function for preplaying Isar steps; may throw exceptions *)
fun preplay_raw _ _ _ _ _ (Let _) = Played Time.zeroTime
  | preplay_raw debug type_enc lam_trans ctxt timeout
      (Prove (_, xs, _, t, subproofs, (fact_names, (meth :: _) :: _))) =
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

      val facts = map (thm_of_proof ctxt) subproofs @ resolve_fact_names ctxt fact_names
      val ctxt' = ctxt |> silence_reconstructors debug

      fun prove () =
        Goal.prove ctxt' [] [] goal (fn {context = ctxt, ...} =>
          HEADGOAL (tac_of_method meth type_enc lam_trans ctxt facts))
        handle ERROR msg => error ("Preplay error: " ^ msg)

      val play_outcome = take_time timeout prove ()
    in
      (if Config.get ctxt trace then preplay_trace ctxt facts goal play_outcome else ();
       play_outcome)
    end


(*** proof preplay interface ***)

type preplay_interface =
  {get_preplay_outcome: label -> play_outcome,
   set_preplay_outcome: label -> play_outcome -> unit,
   preplay_quietly: Time.time -> isar_step -> play_outcome,
   overall_preplay_outcome: isar_proof -> play_outcome}

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

fun merge_preplay_outcomes _ Play_Failed = Play_Failed
  | merge_preplay_outcomes Play_Failed _ = Play_Failed
  | merge_preplay_outcomes (Play_Timed_Out t1) (Play_Timed_Out t2) =
    Play_Timed_Out (Time.+ (t1, t2))
  | merge_preplay_outcomes (Played t1) (Play_Timed_Out t2) = Play_Timed_Out (Time.+ (t1, t2))
  | merge_preplay_outcomes (Play_Timed_Out t1) (Played t2) = Play_Timed_Out (Time.+ (t1, t2))
  | merge_preplay_outcomes (Played t1) (Played t2) = Played (Time.+ (t1, t2))

(* Given a proof, produces an imperative preplay interface with a shared table mapping from labels
   to preplay results. The preplay results are caluclated lazyly and cached to avoid repeated
   calculation.

   Precondition: The proof must be labeled canonically; cf.
   "Slegehammer_Proof.relabel_proof_canonically". *)
fun proof_preplay_interface debug ctxt type_enc lam_trans do_preplay preplay_timeout proof =
  if not do_preplay then
    (* the "dont_preplay" option pretends that everything works just fine *)
    {get_preplay_outcome = K (Played Time.zeroTime),
     set_preplay_outcome = K (K ()),
     preplay_quietly = K (K (Played Time.zeroTime)),
     overall_preplay_outcome = K (Played Time.zeroTime)} : preplay_interface
  else
    let
      val ctxt = enrich_context_with_local_facts proof ctxt

      fun preplay quietly timeout step =
        preplay_raw debug type_enc lam_trans ctxt timeout step
        handle exn =>
               if Exn.is_interrupt exn then
                 reraise exn
               else
                (if not quietly andalso debug then
                   warning ("Preplay failure:\n  " ^ @{make_string} step ^ "\n  " ^
                     @{make_string} exn)
                 else
                   ();
                 Play_Failed)

      (* preplay steps treating exceptions like timeouts *)
      fun preplay_quietly timeout = preplay true timeout

      val preplay_tab =
        let
          fun add_step_to_tab step tab =
            (case label_of_step step of
              NONE => tab
            | SOME l =>
              Canonical_Lbl_Tab.update_new
                (l, (fn () => preplay false preplay_timeout step) |> Lazy.lazy) tab)
            handle Canonical_Lbl_Tab.DUP _ => raise Fail "Sledgehammer_Preplay: preplay time table"
        in
          Canonical_Lbl_Tab.empty
          |> fold_isar_steps add_step_to_tab (steps_of_proof proof)
          |> Unsynchronized.ref
        end

      fun get_preplay_outcome l =
        Canonical_Lbl_Tab.lookup (!preplay_tab) l |> the |> Lazy.force
        handle Option.Option => raise Fail "Sledgehammer_Preplay: preplay time table"

      fun set_preplay_outcome l result =
        preplay_tab := Canonical_Lbl_Tab.update (l, Lazy.value result) (!preplay_tab)

      val result_of_step =
        try (label_of_step #> the #> get_preplay_outcome)
        #> the_default (Played Time.zeroTime)

      fun overall_preplay_outcome (Proof (_, _, steps)) =
        fold_isar_steps (merge_preplay_outcomes o result_of_step) steps (Played Time.zeroTime)
    in
      {get_preplay_outcome = get_preplay_outcome,
       set_preplay_outcome = set_preplay_outcome,
       preplay_quietly = preplay_quietly,
       overall_preplay_outcome = overall_preplay_outcome}
    end

end;
