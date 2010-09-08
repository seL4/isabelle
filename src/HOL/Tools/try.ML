(*  Title:      HOL/Tools/try.ML
    Author:     Jasmin Blanchette, TU Muenchen

Try a combination of proof methods.
*)

signature TRY =
sig
  val invoke_try : Proof.state -> unit
end;

structure Try : TRY =
struct

val timeout = Time.fromSeconds 5

fun can_apply pre post tac st =
  let val {goal, ...} = Proof.goal st in
    case TimeLimit.timeLimit timeout (Seq.pull o tac) (pre st) of
      SOME (x, _) => nprems_of (post x) < nprems_of goal
    | NONE => false
  end

fun do_generic command pre post apply st =
  let val timer = Timer.startRealTimer () in
    if can_apply pre post apply st then
      SOME (command, Time.toMilliseconds (Timer.checkRealTimer timer))
    else
      NONE
  end

fun named_method thy name =
  Method.method thy (Args.src ((name, []), Position.none))

fun apply_named_method name ctxt =
  let val thy = ProofContext.theory_of ctxt in
    Method.apply (named_method thy name) ctxt []
  end

fun do_named_method name st =
  do_generic name (#goal o Proof.goal) snd
             (apply_named_method name (Proof.context_of st)) st

fun apply_named_method_on_first_goal name ctxt =
  let val thy = ProofContext.theory_of ctxt in
    Proof.refine (Method.SelectGoals (1, Method.Basic (named_method thy name)))
  end

fun do_named_method_on_first_goal name st =
  do_generic (name ^ (if nprems_of (#goal (Proof.goal st)) > 1 then "[1]"
                      else "")) I (#goal o Proof.goal)
             (apply_named_method_on_first_goal name (Proof.context_of st)) st

val all_goals_named_methods = ["auto"]
val first_goal_named_methods =
  ["simp", "fast", "fastsimp", "force", "best", "blast", "arith"]
val do_methods =
  map do_named_method_on_first_goal all_goals_named_methods @
  map do_named_method first_goal_named_methods

fun time_string (s, ms) = s ^ ": " ^ string_of_int ms ^ " ms"

fun invoke_try st =
  case do_methods |> Par_List.map (fn f => f st)
                  |> map_filter I |> sort (int_ord o pairself snd) of
    [] => writeln "No proof found."
  | xs as (s, _) :: _ =>
    priority ("Try this command: " ^
        Markup.markup Markup.sendback
            ((if nprems_of (#goal (Proof.goal st)) = 1 then "by" else "apply") ^
             " " ^ s) ^
        ".\n(" ^ space_implode "; " (map time_string xs) ^ ")\n")

val tryN = "try"

val _ =
  Outer_Syntax.improper_command tryN
      "try a combination of proof methods" Keyword.diag
      (Scan.succeed (Toplevel.keep (invoke_try o Toplevel.proof_of)))

end;
