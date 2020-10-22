(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_isar_minimize.ML
    Author:     Steffen Juilf Smolka, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Minimize dependencies (used facts) of Isar proof steps.
*)

signature SLEDGEHAMMER_ISAR_MINIMIZE =
sig
  type isar_step = Sledgehammer_Isar_Proof.isar_step
  type isar_proof = Sledgehammer_Isar_Proof.isar_proof
  type isar_preplay_data = Sledgehammer_Isar_Preplay.isar_preplay_data

  val keep_fastest_method_of_isar_step : isar_preplay_data -> isar_step -> isar_step
  val minimized_isar_step : Proof.context -> thm list -> Time.time -> isar_step ->
    Time.time * isar_step
  val minimize_isar_step_dependencies : Proof.context -> isar_preplay_data Unsynchronized.ref ->
    isar_step -> isar_step
  val postprocess_isar_proof_remove_show_stuttering : isar_proof -> isar_proof
  val postprocess_isar_proof_remove_unreferenced_steps : (isar_step -> isar_step) -> isar_proof ->
    isar_proof
end;

structure Sledgehammer_Isar_Minimize : SLEDGEHAMMER_ISAR_MINIMIZE =
struct

open Sledgehammer_Util
open Sledgehammer_Proof_Methods
open Sledgehammer_Isar_Proof
open Sledgehammer_Isar_Preplay

fun keep_fastest_method_of_isar_step preplay_data
      (Prove {qualifiers, obtains, label, goal, subproofs, facts, proof_methods, comment}) =
    Prove {
      qualifiers = qualifiers,
      obtains = obtains,
      label = label,
      goal = goal,
      subproofs = subproofs,
      facts = facts,
      proof_methods = proof_methods
        |> List.partition (curry (op =) (fastest_method_of_isar_step preplay_data label))
        |> op @,
      comment = comment}
  | keep_fastest_method_of_isar_step _ step = step

val slack = seconds 0.025

fun minimized_isar_step ctxt chained time
    (Prove {qualifiers, obtains, label, goal, subproofs, facts = (lfs0, gfs0),
    proof_methods as meth :: _, comment}) =
  let
    fun mk_step_lfs_gfs lfs gfs =
      Prove {
        qualifiers = qualifiers,
        obtains = obtains,
        label = label,
        goal = goal,
        subproofs = subproofs,
        facts = sort_facts (lfs, gfs),
        proof_methods = proof_methods,
        comment = comment}

    fun minimize_half _ min_facts [] time = (min_facts, time)
      | minimize_half mk_step min_facts (fact :: facts) time =
        (case preplay_isar_step_for_method ctxt chained (time + slack) meth
            (mk_step (min_facts @ facts)) of
          Played time' => minimize_half mk_step min_facts facts time'
        | _ => minimize_half mk_step (fact :: min_facts) facts time)

    val (min_lfs, time') = minimize_half (fn lfs => mk_step_lfs_gfs lfs gfs0) [] lfs0 time
    val (min_gfs, time'') = minimize_half (mk_step_lfs_gfs min_lfs) [] gfs0 time'
  in
    (time'', mk_step_lfs_gfs min_lfs min_gfs)
  end

fun minimize_isar_step_dependencies ctxt preplay_data
      (step as Prove {label = l, proof_methods = meth :: meths, ...}) =
    (case Lazy.force (preplay_outcome_of_isar_step_for_method (!preplay_data) l meth) of
      Played time =>
      let
        fun old_data_for_method meth' =
          (meth', peek_at_outcome (preplay_outcome_of_isar_step_for_method (!preplay_data) l meth'))

        val (time', step') = minimized_isar_step ctxt [] time step
      in
        set_preplay_outcomes_of_isar_step ctxt time' preplay_data step'
          ((meth, Played time') :: (if step' = step then map old_data_for_method meths else []));
        step'
      end
    | _ => step (* don't touch steps that time out or fail *))
  | minimize_isar_step_dependencies _ _ step = step

fun postprocess_isar_proof_remove_show_stuttering (proof as Proof {steps, ...}) =
  let
    fun process_steps [] = []
      | process_steps (steps as [
          Prove (p1 as {qualifiers = [], obtains = [], goal = t1, ...}),
          Prove (p2 as {qualifiers = [Show], obtains = [], goal = t2, ...})]) =
        if t1 aconv t2 then
          [Prove {
             qualifiers = [Show],
             obtains = [],
             label = #label p2,
             goal = t2,
             subproofs = #subproofs p1,
             facts = #facts p1,
             proof_methods = #proof_methods p1,
             comment = #comment p1 ^ #comment p2}]
        else steps
      | process_steps (step :: steps) = step :: process_steps steps
  in
    isar_proof_with_steps proof (process_steps steps)
  end

fun postprocess_isar_proof_remove_unreferenced_steps postproc_step =
  let
    fun process_proof (proof as Proof {steps, ...}) =
      process_steps steps ||> isar_proof_with_steps proof
    and process_steps [] = ([], [])
      | process_steps steps =
        (* the last step is always implicitly referenced *)
        let val (steps, (used, concl)) = split_last steps ||> process_used_step in
          fold_rev process_step steps (used, [concl])
        end
    and process_step step (used, accu) =
      (case label_of_isar_step step of
        NONE => (used, step :: accu)
      | SOME l =>
        if Ord_List.member label_ord used l then
          process_used_step step |>> Ord_List.union label_ord used ||> (fn step => step :: accu)
        else
          (used, accu))
    and process_used_step step = process_used_step_subproofs (postproc_step step)
    and process_used_step_subproofs (Prove {qualifiers, obtains, label, goal, subproofs,
          facts = (lfs, gfs), proof_methods, comment}) =
      let
        val (used, subproofs') =
          map process_proof subproofs
          |> split_list
          |>> Ord_List.unions label_ord
          |>> fold (Ord_List.insert label_ord) lfs
        val prove = Prove {
          qualifiers = qualifiers,
          obtains = obtains,
          label = label,
          goal = goal,
          subproofs = subproofs',
          facts = (lfs, gfs),
          proof_methods = proof_methods,
          comment = comment}
      in
        (used, prove)
      end
  in
    snd o process_proof
  end

end;
