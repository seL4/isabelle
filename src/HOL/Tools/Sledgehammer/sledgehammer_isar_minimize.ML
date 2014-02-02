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

  val minimize_isar_step_dependencies : isar_preplay_data -> isar_step -> isar_step
  val postprocess_isar_proof_remove_unreferenced_steps : (isar_step -> isar_step) -> isar_proof ->
    isar_proof
end;

structure Sledgehammer_Isar_Minimize : SLEDGEHAMMER_ISAR_MINIMIZE =
struct

open Sledgehammer_Reconstructor
open Sledgehammer_Isar_Proof
open Sledgehammer_Isar_Preplay

val slack = seconds 0.1

fun minimize_isar_step_dependencies (_ : isar_preplay_data) (step as Let _) = step
  | minimize_isar_step_dependencies
      {reset_preplay_outcomes, set_preplay_outcome, preplay_outcome, preplay_quietly, ...}
      (step as Prove (qs, xs, l, t, subproofs, ((lfs, gfs), methss as (meth :: _) :: _))) =
    (case Lazy.force (preplay_outcome l meth) of
      Played time =>
      let
        fun mk_step_lfs_gfs lfs gfs = Prove (qs, xs, l, t, subproofs, ((lfs, gfs), methss))
        val mk_step_gfs_lfs = curry (swap #> uncurry mk_step_lfs_gfs)

        fun minimize_facts _ time min_facts [] = (time, min_facts)
          | minimize_facts mk_step time min_facts (f :: facts) =
            (case preplay_quietly (Time.+ (time, slack)) (mk_step (min_facts @ facts)) of
              Played time => minimize_facts mk_step time min_facts facts
            | _ => minimize_facts mk_step time (f :: min_facts) facts)

        val (time, min_lfs) = minimize_facts (mk_step_gfs_lfs gfs) time [] lfs
        val (time, min_gfs) = minimize_facts (mk_step_lfs_gfs min_lfs) time [] gfs

        val step' = mk_step_lfs_gfs min_lfs min_gfs
      in
        reset_preplay_outcomes step';
        set_preplay_outcome l meth (Played time);
        step'
      end
    | _ => step (* don't touch steps that time out or fail *))

fun postprocess_isar_proof_remove_unreferenced_steps postproc_step =
  let
    val add_lfs = fold (Ord_List.insert label_ord)

    fun do_proof (Proof (fix, assms, steps)) =
      let val (refed, steps) = do_steps steps in
        (refed, Proof (fix, assms, steps))
      end
    and do_steps [] = ([], [])
      | do_steps steps =
        (* the last step is always implicitly referenced *)
        let val (steps, (refed, concl)) = split_last steps ||> do_refed_step in
          fold_rev do_step steps (refed, [concl])
        end
    and do_step step (refed, accu) =
      (case label_of_isar_step step of
        NONE => (refed, step :: accu)
      | SOME l =>
        if Ord_List.member label_ord refed l then
          do_refed_step step
          |>> Ord_List.union label_ord refed
          ||> (fn x => x :: accu)
        else
          (refed, accu))
    and do_refed_step step = step |> postproc_step |> do_refed_step'
    and do_refed_step' (Let _) = raise Fail "Sledgehammer_Isar_Minimize"
      | do_refed_step' (Prove (qs, xs, l, t, subproofs, ((lfs, gfs), m))) =
        let
          val (refed, subproofs) =
            map do_proof subproofs
            |> split_list
            |>> Ord_List.unions label_ord
            |>> add_lfs lfs
          val step = Prove (qs, xs, l, t, subproofs, ((lfs, gfs), m))
        in
          (refed, step)
        end
  in
    snd o do_proof
  end

end;
