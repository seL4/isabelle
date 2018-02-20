(*  Title:      Pure/par_tactical.ML
    Author:     Makarius

Parallel tacticals.
*)

signature BASIC_PAR_TACTICAL =
sig
  val PARALLEL_CHOICE: tactic list -> tactic
  val PARALLEL_GOALS: tactic -> tactic
  val PARALLEL_ALLGOALS: (int -> tactic) -> tactic
end;

signature PAR_TACTICAL =
sig
  include BASIC_PAR_TACTICAL
end;

structure Par_Tactical: PAR_TACTICAL =
struct

(* parallel choice of single results *)

fun PARALLEL_CHOICE tacs st =
  (case Par_List.get_some (fn tac => SINGLE tac st) tacs of
    NONE => Seq.empty
  | SOME st' => Seq.single st');


(* parallel refinement of non-schematic goal by single results *)

local

exception FAILED of unit;

fun retrofit st' =
  rotate_prems ~1 #>
  Thm.bicompose NONE {flatten = false, match = false, incremented = false}
      (false, Goal.conclude st', Thm.nprems_of st') 1;

in

fun PARALLEL_GOALS tac st =
  let
    val goals =
      Drule.strip_imp_prems (Thm.cprop_of st)
      |> map (Thm.adjust_maxidx_cterm ~1);
  in
    if Multithreading.relevant goals andalso forall (fn g => Thm.maxidx_of_cterm g = ~1) goals then
      let
        fun try_goal g =
          (case SINGLE tac (Goal.init g) of
            NONE => raise FAILED ()
          | SOME st' => st');
        val results = Par_List.map try_goal goals;
      in EVERY (map retrofit (rev results)) st
      end handle FAILED () => Seq.empty
    else DETERM tac st
  end;

end;

val PARALLEL_ALLGOALS = PARALLEL_GOALS o ALLGOALS;

end;

structure Basic_Par_Tactical: BASIC_PAR_TACTICAL = Par_Tactical;
open Basic_Par_Tactical;
