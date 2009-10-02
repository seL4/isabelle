(*  Title:      Tools/auto_solve.ML
    Author:     Timothy Bourke and Gerwin Klein, NICTA

Check whether a newly stated theorem can be solved directly by an
existing theorem.  Duplicate lemmas can be detected in this way.

The implementation is based in part on Berghofer and Haftmann's
quickcheck.ML.  It relies critically on the FindTheorems solves
feature.
*)

signature AUTO_SOLVE =
sig
  val auto : bool Unsynchronized.ref
  val auto_time_limit : int Unsynchronized.ref
  val limit : int Unsynchronized.ref
end;

structure Auto_Solve : AUTO_SOLVE =
struct

(* preferences *)

val auto = Unsynchronized.ref false;
val auto_time_limit = Unsynchronized.ref 2500;
val limit = Unsynchronized.ref 5;

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
  (setmp auto true (fn () =>
    Preferences.bool_pref auto
      "auto-solve"
      "Try to solve newly declared lemmas with existing theorems.") ());

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
    (Preferences.nat_pref auto_time_limit
      "auto-solve-time-limit"
      "Time limit for seeking automatic solutions (in milliseconds).");


(* hook *)

val _ = Context.>> (Specification.add_theorem_hook (fn int => fn state =>
  let
    val ctxt = Proof.context_of state;

    val crits = [(true, FindTheorems.Solves)];
    fun find g = snd (FindTheorems.find_theorems ctxt (SOME g) (SOME (! limit)) false crits);

    fun prt_result (goal, results) =
      let
        val msg =
          (case goal of
            NONE => "The current goal"
          | SOME sg => Syntax.string_of_term ctxt (Thm.term_of sg));
      in
        Pretty.big_list
          (msg ^ " could be solved directly with:")
          (map (FindTheorems.pretty_thm ctxt) results)
      end;

    fun seek_against_goal () =
      (case try Proof.flat_goal state of
        NONE => NONE
      | SOME (_, st) =>
          let
            val subgoals = Drule.strip_imp_prems (Thm.cprop_of st);
            val rs =
              if length subgoals = 1
              then [(NONE, find st)]
              else map (fn sg => (SOME sg, find (Goal.init sg))) subgoals;
            val results = filter_out (null o snd) rs;
          in if null results then NONE else SOME results end);

    fun go () =
      let
        val res =
          TimeLimit.timeLimit (Time.fromMilliseconds (! auto_time_limit))
            (try seek_against_goal) ();
      in
        (case res of
          SOME (SOME results) =>
            state |> Proof.goal_message
              (fn () => Pretty.chunks
                [Pretty.str "",
                  Pretty.markup Markup.hilite
                    (separate (Pretty.brk 0) (map prt_result results))])
        | _ => state)
      end handle TimeLimit.TimeOut => (warning "Auto solve: timeout"; state);
  in
    if int andalso ! auto andalso not (! Toplevel.quiet)
    then go ()
    else state
  end));

end;

val auto_solve = Auto_Solve.auto;
val auto_solve_time_limit = Auto_Solve.auto_time_limit;

