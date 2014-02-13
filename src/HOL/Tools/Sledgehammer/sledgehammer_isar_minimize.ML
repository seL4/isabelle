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
  val minimize_isar_step_dependencies : Proof.context -> bool ->
    isar_preplay_data Unsynchronized.ref -> isar_step -> isar_step
  val postprocess_isar_proof_remove_unreferenced_steps : (isar_step -> isar_step) -> isar_proof ->
    isar_proof
end;

structure Sledgehammer_Isar_Minimize : SLEDGEHAMMER_ISAR_MINIMIZE =
struct

open Sledgehammer_Proof_Methods
open Sledgehammer_Isar_Proof
open Sledgehammer_Isar_Preplay

fun keep_fastest_method_of_isar_step preplay_data
      (Prove (qs, xs, l, t, subproofs, facts, meths, comment)) =
    Prove (qs, xs, l, t, subproofs, facts,
      meths |> List.partition (curry (op =) (fastest_method_of_isar_step preplay_data l)) |> op @,
      comment)
  | keep_fastest_method_of_isar_step _ step = step

val slack = seconds 0.025

fun minimize_isar_step_dependencies ctxt debug preplay_data
      (step as Prove (qs, xs, l, t, subproofs, (lfs0, gfs0), meths as meth :: _, comment)) =
    (case Lazy.force (preplay_outcome_of_isar_step_for_method (!preplay_data) l meth) of
      Played time =>
      let
        fun mk_step_lfs_gfs lfs gfs = Prove (qs, xs, l, t, subproofs, (lfs, gfs), meths, comment)

        fun minimize_facts _ min_facts [] time = (min_facts, time)
          | minimize_facts mk_step min_facts (fact :: facts) time =
            (case preplay_isar_step_for_method ctxt debug (Time.+ (time, slack)) meth
                (mk_step (min_facts @ facts)) of
              Played time' => minimize_facts mk_step min_facts facts time'
            | _ => minimize_facts mk_step (fact :: min_facts) facts time)

        val (min_lfs, time') = minimize_facts (fn lfs => mk_step_lfs_gfs lfs gfs0) [] lfs0 time
        val (min_gfs, time'') = minimize_facts (mk_step_lfs_gfs min_lfs) [] gfs0 time'

        val step' = mk_step_lfs_gfs min_lfs min_gfs
      in
        set_preplay_outcomes_of_isar_step ctxt debug time'' preplay_data step'
          [(meth, Played time'')];
        step'
      end
    | _ => step (* don't touch steps that time out or fail *))
  | minimize_isar_step_dependencies _ _ _ step = step

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
    and process_used_step_subproofs (Prove (qs, xs, l, t, subproofs, (lfs, gfs), meths, comment)) =
      let
        val (used, subproofs) =
          map process_proof subproofs
          |> split_list
          |>> Ord_List.unions label_ord
          |>> fold (Ord_List.insert label_ord) lfs
      in
        (used, Prove (qs, xs, l, t, subproofs, (lfs, gfs), meths, comment))
      end
  in
    snd o process_proof
  end

end;
