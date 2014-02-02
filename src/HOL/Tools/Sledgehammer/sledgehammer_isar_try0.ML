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

fun step_with_method meth (Prove (qs, xs, l, t, subproofs, (facts, _))) =
  Prove (qs, xs, l, t, subproofs, (facts, [meth]))

val slack = seconds 0.05

fun try0_step _ _ (step as Let _) = step
  | try0_step preplay_timeout
      ({preplay_step, set_preplay_outcomes, preplay_outcome, ...} : isar_preplay_data)
      (step as Prove (_, _, l, _, _, (_, meths as meth :: _))) =
    let
      val timeout =
        (case Lazy.force (preplay_outcome l meth) of
          Played time => Time.+ (time, slack)
        | _ => preplay_timeout)

      fun try_method meth =
        (case preplay_step timeout meth step of
          outcome as Played _ => SOME (meth, outcome)
        | _ => NONE)
    in
      (* FIXME: create variant after success *)
      (case Par_List.get_some try_method meths of
        SOME (meth', outcome) =>
        (set_preplay_outcomes l [(meth', Lazy.value outcome)]; step_with_method meth' step)
      | NONE => step)
    end

val try0_isar_proof = map_isar_steps oo try0_step

end;
