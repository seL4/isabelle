(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_try0.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Try replacing calls to metis with calls to other proof methods in order to
speed up proofs, eliminate dependencies, and repair broken proof steps.
*)

signature SLEDGEHAMMER_TRY0 =
sig
  type isar_proof = Sledgehammer_Proof.isar_proof
  type preplay_interface = Sledgehammer_Preplay.preplay_interface

  val try0 : Time.time -> preplay_interface -> isar_proof -> isar_proof
end

structure Sledgehammer_Try0 : SLEDGEHAMMER_TRY0 =
struct

open Sledgehammer_Proof
open Sledgehammer_Preplay

fun variants (Let _) = raise Fail "Sledgehammer_Try0: variants"
  | variants (Prove (qs, xs, l, t, subproofs, By (facts, _))) =
      let
        val methods = [SimpM, AutoM, FastforceM, ArithM]
        fun step method = Prove (qs, xs, l, t, subproofs, By (facts, method))
        (*fun step_without_facts method =
          Prove (qs, xs, l, t, subproofs, By (no_facts, method))*)
      in
        (* FIXME *)
        (* There seems to be a bias for methods earlier in the list, so we put
           the variants using no facts first. *)
        (*map step_without_facts methods @*) map step methods
      end

fun try0_step _ _ (step as Let _) = step
  | try0_step preplay_timeout ({preplay_quietly, get_time, set_time,
    set_preplay_fail, ...} : preplay_interface)
    (step as Prove (_, _, l, _, _, _)) =
      let

        val (preplay_fail, timeout) =
          case get_time l of
            (true, _) => (true, preplay_timeout)
          | (false, t) => (false, t)

        fun try_variant variant =
           case preplay_quietly timeout variant of
             (true, _) => NONE
           | time as (false, _) => SOME (variant, time)

      in
        case Par_List.get_some try_variant (variants step) of
          SOME (step, time) => (set_time l time; step)
        | NONE => (if preplay_fail then set_preplay_fail true else (); step)
      end

fun try0 preplay_timeout
  (preplay_interface as {set_preplay_fail, ...} : preplay_interface) proof =
    (set_preplay_fail false; (* failure might be fixed *)
     map_isar_steps (try0_step preplay_timeout preplay_interface) proof)

end
