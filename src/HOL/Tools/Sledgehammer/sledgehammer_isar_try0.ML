(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_isar_try0.ML
    Author:     Steffen Juilf Smolka, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Try replacing calls to "metis" with calls to other proof methods to speed up proofs, eliminate
dependencies, and repair broken proof steps.
*)

signature SLEDGEHAMMER_ISAR_TRY0 =
sig
  type isar_proof = Sledgehammer_Isar_Proof.isar_proof
  type isar_preplay_data = Sledgehammer_Isar_Preplay.isar_preplay_data

  val try0_isar_proof : Time.time -> isar_preplay_data -> isar_proof -> isar_proof
end;

structure Sledgehammer_Isar_Try0 : SLEDGEHAMMER_ISAR_TRY0 =
struct

open Sledgehammer_Util
open Sledgehammer_Reconstructor
open Sledgehammer_Isar_Proof
open Sledgehammer_Isar_Preplay

fun variants_of_step (Prove (qs, xs, l, t, subproofs, (facts, methss))) =
    map (fn meth => Prove (qs, xs, l, t, subproofs, (facts, [[meth]]))) (tl (flat methss))
  | variants_of_step _ = raise Fail "Sledgehammer_Isar_Try0: variants_of_step"

val slack = seconds 0.05

fun try0_step _ _ (step as Let _) = step
  | try0_step preplay_timeout
      ({get_preplay_outcome, set_preplay_outcome, preplay_quietly, ...} : isar_preplay_data)
      (step as Prove (_, _, l, _, _, _)) =
    let
      val timeout =
        (case get_preplay_outcome l of
          Played time => Time.+ (time, slack)
        | _ => preplay_timeout)

      fun try_variant variant =
        (case preplay_quietly timeout variant of
          result as Played _ => SOME (variant, result)
        | _ => NONE)
    in
      (case Par_List.get_some try_variant (variants_of_step step) of
        SOME (step', result) => (set_preplay_outcome l result; step')
      | NONE => step)
    end

val try0_isar_proof = map_isar_steps oo try0_step

end;
