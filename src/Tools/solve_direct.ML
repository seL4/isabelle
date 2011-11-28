(*  Title:      Tools/solve_direct.ML
    Author:     Timothy Bourke and Gerwin Klein, NICTA

Check whether a newly stated theorem can be solved directly by an
existing theorem.  Duplicate lemmas can be detected in this way.

The implementation relies critically on the Find_Theorems solves
feature.
*)

signature SOLVE_DIRECT =
sig
  val solve_directN: string
  val someN: string
  val noneN: string
  val unknownN: string
  val auto: bool Unsynchronized.ref
  val max_solutions: int Unsynchronized.ref
  val solve_direct: Proof.state -> bool * (string * Proof.state)
  val setup: theory -> theory
end;

structure Solve_Direct: SOLVE_DIRECT =
struct

datatype mode = Auto_Try | Try | Normal

val solve_directN = "solve_direct";

val someN = "some";
val noneN = "none";
val unknownN = "none";

(* preferences *)

val auto = Unsynchronized.ref false;
val max_solutions = Unsynchronized.ref 5;

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
  (Unsynchronized.setmp auto true (fn () =>
    Preferences.bool_pref auto
      "auto-solve-direct"
      ("Run " ^ quote solve_directN ^ " automatically.")) ());


(* solve_direct command *)

fun do_solve_direct mode state =
  let
    val ctxt = Proof.context_of state;

    val crits = [(true, Find_Theorems.Solves)];
    fun find g =
      snd (Find_Theorems.find_theorems ctxt (SOME g) (SOME (! max_solutions)) false crits);

    fun prt_result (goal, results) =
      let
        val msg =
          (if mode = Auto_Try then "Auto " else "") ^ solve_directN ^ ": " ^
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
    fun message results = separate (Pretty.brk 0) (map prt_result results);
  in
    (case try seek_against_goal () of
      SOME (SOME results) =>
        (someN,
          state |>
            (if mode = Auto_Try then
               Proof.goal_message
                 (fn () =>
                   Pretty.chunks
                    [Pretty.str "", Pretty.markup Isabelle_Markup.hilite (message results)])
             else
               tap (fn _ =>
                 Output.urgent_message (Pretty.string_of (Pretty.chunks (message results))))))
    | SOME NONE =>
        (if mode = Normal then Output.urgent_message "No proof found."
         else ();
         (noneN, state))
    | NONE =>
        (if mode = Normal then Output.urgent_message "An error occurred."
         else ();
         (unknownN, state)))
  end
  |> `(fn (outcome_code, _) => outcome_code = someN);

val solve_direct = do_solve_direct Normal

val _ =
  Outer_Syntax.improper_command solve_directN
    "try to solve conjectures directly with existing theorems" Keyword.diag
    (Scan.succeed
      (Toplevel.keep (ignore o solve_direct o Toplevel.proof_of)));


(* hook *)

fun try_solve_direct auto = do_solve_direct (if auto then Auto_Try else Try)

val setup = Try.register_tool (solve_directN, (10, auto, try_solve_direct));

end;
