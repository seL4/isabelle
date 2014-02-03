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
  val minimize_isar_step_dependencies : Proof.context -> isar_preplay_data Unsynchronized.ref ->
    isar_step -> isar_step
  val postprocess_isar_proof_remove_unreferenced_steps : (isar_step -> isar_step) -> isar_proof ->
    isar_proof
end;

structure Sledgehammer_Isar_Minimize : SLEDGEHAMMER_ISAR_MINIMIZE =
struct

open Sledgehammer_Reconstructor
open Sledgehammer_Isar_Proof
open Sledgehammer_Isar_Preplay

fun keep_fastest_method_of_isar_step preplay_data
      (Prove (qs, xs, l, t, subproofs, (facts, _))) =
    Prove (qs, xs, l, t, subproofs, (facts, [fastest_method_of_isar_step preplay_data l]))
  | keep_fastest_method_of_isar_step _ step = step

val slack = seconds 0.1

fun minimize_isar_step_dependencies ctxt preplay_data
      (step as Prove (qs, xs, l, t, subproofs, ((lfs, gfs), meths as meth :: _))) =
    (case Lazy.force (preplay_outcome_of_isar_step_for_method (!preplay_data) l meth) of
      Played time =>
      let
        fun mk_step_lfs_gfs lfs gfs = Prove (qs, xs, l, t, subproofs, ((lfs, gfs), meths))

        fun minimize_facts _ time min_facts [] = (time, min_facts)
          | minimize_facts mk_step time min_facts (f :: facts) =
            (case preplay_isar_step ctxt (Time.+ (time, slack)) meth
                (mk_step (min_facts @ facts)) of
              Played time => minimize_facts mk_step time min_facts facts
            | _ => minimize_facts mk_step time (f :: min_facts) facts)

        val (time, min_lfs) = minimize_facts (fn lfs => mk_step_lfs_gfs lfs gfs) time [] lfs
        val (time, min_gfs) = minimize_facts (mk_step_lfs_gfs min_lfs) time [] gfs

        val step' = mk_step_lfs_gfs min_lfs min_gfs
      in
        set_preplay_outcomes_of_isar_step ctxt time preplay_data step'
          [(meth, Lazy.value (Played time))];
        step'
      end
    | _ => step (* don't touch steps that time out or fail *))
  | minimize_isar_step_dependencies _ _ step = step

fun postprocess_isar_proof_remove_unreferenced_steps postproc_step =
  let
    fun process_proof (Proof (fix, assms, steps)) =
      process_steps steps ||> (fn steps => Proof (fix, assms, steps))
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
    and process_used_step step = step |> postproc_step |> process_used_step_subproofs
    and process_used_step_subproofs (Prove (qs, xs, l, t, subproofs, ((lfs, gfs), meths))) =
      let
        val (used, subproofs) =
          map process_proof subproofs
          |> split_list
          |>> Ord_List.unions label_ord
          |>> fold (Ord_List.insert label_ord) lfs
        val step = Prove (qs, xs, l, t, subproofs, ((lfs, gfs), meths))
      in
        (used, step)
      end
  in
    snd o process_proof
  end

end;
