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
  val strip_goals: thm -> cterm list option
  val retrofit_tac: {close: bool} -> thm list -> tactic
end;

structure Par_Tactical: PAR_TACTICAL =
struct

(* parallel choice of single results *)

fun PARALLEL_CHOICE tacs st =
  (case Par_List.get_some (fn tac => SINGLE tac st) tacs of
    NONE => Seq.empty
  | SOME st' => Seq.single st');


(* parallel refinement of non-schematic goal by single results *)

fun strip_goals st =
  let
    val goals =
      Drule.strip_imp_prems (Thm.cprop_of st)
      |> map (Thm.adjust_maxidx_cterm ~1);
  in
    if not (null goals) andalso forall (fn g => Thm.maxidx_of_cterm g = ~1) goals
    then SOME goals else NONE
  end;

local

exception FAILED of unit;

fun retrofit {close} st' =
  rotate_prems ~1 #>
  Thm.bicompose NONE {flatten = false, match = false, incremented = false}
      (false, Goal.conclude st' |> close ? Thm.close_derivation \<^here>, Thm.nprems_of st') 1;

in

fun retrofit_tac close = EVERY o map (retrofit close);

fun PARALLEL_GOALS tac st =
  (case strip_goals st of
    SOME goals =>
      if Future.relevant goals then
        let
          fun try_goal g =
            (case SINGLE tac (Goal.init g) of
              NONE => raise FAILED ()
            | SOME st' => st');
          val results = Par_List.map try_goal goals;
        in retrofit_tac {close = false} (rev results) st end handle FAILED () => Seq.empty
      else DETERM tac st
  | NONE => DETERM tac st);

end;

val PARALLEL_ALLGOALS = PARALLEL_GOALS o ALLGOALS;

end;

structure Basic_Par_Tactical: BASIC_PAR_TACTICAL = Par_Tactical;
open Basic_Par_Tactical;
