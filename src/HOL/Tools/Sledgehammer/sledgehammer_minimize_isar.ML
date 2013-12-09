(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_minimize_isar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Minimize dependencies (used facts) of Isar proof steps.
*)

signature SLEDGEHAMMER_MINIMIZE_ISAR =
sig
  type preplay_interface = Sledgehammer_Preplay.preplay_interface
  type isar_proof = Sledgehammer_Proof.isar_proof
  val minimize_dependencies_and_remove_unrefed_steps :
    bool -> preplay_interface -> isar_proof -> isar_proof
end;

structure Sledgehammer_Minimize_Isar : SLEDGEHAMMER_MINIMIZE_ISAR =
struct

open Sledgehammer_Util
open Sledgehammer_Proof
open Sledgehammer_Preplay

val slack = 1.3

fun min_deps_of_step (_ : preplay_interface) (step as Let _) = step
  | min_deps_of_step {get_preplay_time, set_preplay_time, preplay_quietly, ...}
      (step as Prove (qs, xs, l, t, subproofs, ((lfs, gfs), method))) =
  (case get_preplay_time l of
    (* don't touch steps that time out or fail; minimizing won't help *)
    (true, _) => step
  | (false, time) =>
    let
      fun mk_step_lfs_gfs lfs gfs =
        Prove (qs, xs, l, t, subproofs, ((lfs, gfs), method))
      val mk_step_gfs_lfs = curry (swap #> uncurry mk_step_lfs_gfs)

      fun minimize_facts _ time min_facts [] = (time, min_facts)
        | minimize_facts mk_step time min_facts (f :: facts) =
          (case preplay_quietly (time_mult slack time)
                  (mk_step (min_facts @ facts)) of
            (true, _) => minimize_facts mk_step time (f :: min_facts) facts
          | (false, time) => minimize_facts mk_step time min_facts facts)

      val (time, min_lfs) = minimize_facts (mk_step_gfs_lfs gfs) time [] lfs
      val (time, min_gfs) = minimize_facts (mk_step_lfs_gfs min_lfs) time [] gfs

    in
      set_preplay_time l (false, time);
      mk_step_lfs_gfs min_lfs min_gfs
    end)

fun minimize_dependencies_and_remove_unrefed_steps isar_try0 preplay_interface
        proof =
  let
    fun cons_to xs x = x :: xs

    val add_lfs = fold (Ord_List.insert label_ord)

    fun do_proof (Proof (fix, assms, steps)) =
      let
        val (refed, steps) = do_steps steps
      in
        (refed, Proof (fix, assms, steps))
      end

    and do_steps steps =
      let
        (* the last step is always implicitly referenced *)
        val (steps, (refed, concl)) =
          split_last steps
          ||> do_refed_step
      in
        fold_rev do_step steps (refed, [concl])
      end

    and do_step step (refed, accu) =
      case label_of_step step of
        NONE => (refed, step :: accu)
      | SOME l =>
          if Ord_List.member label_ord refed l then
            do_refed_step step
            |>> Ord_List.union label_ord refed
            ||> cons_to accu
          else
            (refed, accu)

    and do_refed_step step =
      step
      |> isar_try0 ? min_deps_of_step preplay_interface
      |> do_refed_step'

    and do_refed_step' (Let _) = raise Fail "Sledgehammer_Minimize_Isar"
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
    snd (do_proof proof)
  end

end;
