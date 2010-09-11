(*  Title:      Tools/auto_solve.ML
    Author:     Timothy Bourke and Gerwin Klein, NICTA

Check whether a newly stated theorem can be solved directly by an
existing theorem.  Duplicate lemmas can be detected in this way.

The implementation relies critically on the Find_Theorems solves
feature.
*)

signature AUTO_SOLVE =
sig
  val auto : bool Unsynchronized.ref
  val max_solutions : int Unsynchronized.ref
  val setup : theory -> theory
end;

structure Auto_Solve : AUTO_SOLVE =
struct

(* preferences *)

val auto = Unsynchronized.ref false;
val max_solutions = Unsynchronized.ref 5;

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
  (setmp_noncritical auto true (fn () =>
    Preferences.bool_pref auto
      "auto-solve" "Try to solve conjectures with existing theorems.") ());


(* hook *)

fun auto_solve state =
  let
    val ctxt = Proof.context_of state;

    val crits = [(true, Find_Theorems.Solves)];
    fun find g = snd (Find_Theorems.find_theorems ctxt (SOME g) (SOME (! max_solutions)) false crits);

    fun prt_result (goal, results) =
      let
        val msg =
          (case goal of
            NONE => "The current goal"
          | SOME sg => Syntax.string_of_term ctxt (Thm.term_of sg));
      in
        Pretty.big_list
          (msg ^ " could be solved directly with:")
          (map (Find_Theorems.pretty_thm ctxt) results)
      end;

    fun seek_against_goal () =
      (case try Proof.simple_goal state of
        NONE => NONE
      | SOME {goal = st, ...} =>
          let
            val subgoals = Drule.strip_imp_prems (Thm.cprop_of st);
            val rs =
              if length subgoals = 1
              then [(NONE, find st)]
              else map (fn sg => (SOME sg, find (Goal.init sg))) subgoals;
            val results = filter_out (null o snd) rs;
          in if null results then NONE else SOME results end);

    fun go () =
      (case try seek_against_goal () of
        SOME (SOME results) =>
          (true, state |> Proof.goal_message
                  (fn () => Pretty.chunks
                    [Pretty.str "",
                      Pretty.markup Markup.hilite
                        (separate (Pretty.brk 0) (map prt_result results))]))
      | _ => (false, state));
  in if not (!auto) then (false, state) else go () end;

val setup = Auto_Tools.register_tool ("solve", auto_solve)

end;
