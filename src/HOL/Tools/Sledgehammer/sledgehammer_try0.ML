(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_try0.ML
    Author:     Steffen Juilf Smolka, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Try replacing calls to metis with calls to other proof methods to speed up proofs, eliminate
dependencies, and repair broken proof steps.
*)

signature SLEDGEHAMMER_TRY0 =
sig
  type isar_proof = Sledgehammer_Proof.isar_proof
  type preplay_interface = Sledgehammer_Preplay.preplay_interface

  val try0 : Time.time -> preplay_interface -> isar_proof -> isar_proof
end;

structure Sledgehammer_Try0 : SLEDGEHAMMER_TRY0 =
struct

open Sledgehammer_Util
open Sledgehammer_Proof
open Sledgehammer_Preplay

fun variants_of_step (Prove (qs, xs, l, t, subproofs, (facts, methss))) =
    map (fn meth => Prove (qs, xs, l, t, subproofs, (facts, [[meth]]))) (tl (flat methss))
  | variants_of_step _ = raise Fail "Sledgehammer_Try0: variants_of_step"

val slack = seconds 0.05

fun try0_step _ _ (step as Let _) = step
  | try0_step preplay_timeout
      ({preplay_quietly, get_preplay_time, set_preplay_time, ...} : preplay_interface)
      (step as Prove (_, _, l, _, _, _)) =
    let
      val timeout =
        (case get_preplay_time l of
          (true, _) => preplay_timeout
        | (false, t) => Time.+ (t, slack))

      fun try_variant variant =
        (case preplay_quietly timeout variant of
          (true, _) => NONE
        | time as (false, _) => SOME (variant, time))
    in
      (case Par_List.get_some try_variant (variants_of_step step) of
        SOME (step, time) => (set_preplay_time l time; step)
      | NONE => step)
    end

val try0 = map_isar_steps oo try0_step

end;
