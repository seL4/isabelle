(*  Title:      Tools/solve_direct.ML
    Author:     Timothy Bourke and Gerwin Klein, NICTA

Check whether a newly stated theorem can be solved directly by an
existing theorem.  Duplicate lemmas can be detected in this way.

The implementation relies critically on the Find_Theorems solves
feature.
*)

signature SOLVE_DIRECT =
sig
  val auto : bool Unsynchronized.ref
  val max_solutions : int Unsynchronized.ref
  val setup : theory -> theory
end;

structure Solve_Direct : SOLVE_DIRECT =
struct

val solve_directN = "solve_direct"

(* preferences *)

val auto = Unsynchronized.ref false;
val max_solutions = Unsynchronized.ref 5;

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
  (Unsynchronized.setmp auto true (fn () =>
    Preferences.bool_pref auto
      ("Auto " ^ solve_directN)
      ("Run " ^ quote solve_directN ^ " automatically.")) ());

fun solve_direct auto state =
  let
    val ctxt = Proof.context_of state;

    val crits = [(true, Find_Theorems.Solves)];
    fun find g = snd (Find_Theorems.find_theorems ctxt (SOME g) (SOME (! max_solutions)) false crits);

    fun prt_result (goal, results) =
      let
        val msg =
          (if auto then "Auto " else "") ^ solve_directN ^ ": " ^
          (case goal of
            NONE => "The current goal"
          | SOME sg => Syntax.string_of_term ctxt (Thm.term_of sg));
      in
        Pretty.big_list
          (msg ^ " can be solved directly with")
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
    fun message results = separate (Pretty.brk 0) (map prt_result results)
  in
    (case try seek_against_goal () of
      SOME (SOME results) =>
      (true, state |> (if auto then
                         Proof.goal_message
                           (fn () => Pretty.chunks
                              [Pretty.str "",
                               Pretty.markup Markup.hilite (message results)])
                       else
                         tap (fn _ => priority (Pretty.string_of
                                (Pretty.chunks (message results))))))
    | _ => (false, state))
  end;

val invoke_solve_direct = fst o solve_direct false

val _ =
  Outer_Syntax.improper_command solve_directN
      "try to solve conjectures directly with existing theorems" Keyword.diag
      (Scan.succeed (Toplevel.keep (K () o invoke_solve_direct
                                    o Toplevel.proof_of)))

(* hook *)

fun auto_solve_direct state =
  if not (!auto) then (false, state) else solve_direct true state

val setup = Auto_Tools.register_tool (solve_directN, auto_solve_direct)

end;
