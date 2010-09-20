(*  Title:      HOL/Tools/try.ML
    Author:     Jasmin Blanchette, TU Muenchen

Try a combination of proof methods.
*)

signature TRY =
sig
  val auto : bool Unsynchronized.ref
  val invoke_try : Time.time option -> Proof.state -> bool
  val setup : theory -> theory
end;

structure Try : TRY =
struct

val auto = Unsynchronized.ref false

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
  (setmp_noncritical auto true (fn () =>
    Preferences.bool_pref auto
      "auto-try" "Try standard proof methods.") ());

val default_timeout = Time.fromSeconds 5

fun can_apply timeout_opt pre post tac st =
  let val {goal, ...} = Proof.goal st in
    case (case timeout_opt of
            SOME timeout => TimeLimit.timeLimit timeout
          | NONE => fn f => fn x => f x) (Seq.pull o tac) (pre st) of
      SOME (x, _) => nprems_of (post x) < nprems_of goal
    | NONE => false
  end

fun do_generic timeout_opt command pre post apply st =
  let val timer = Timer.startRealTimer () in
    if can_apply timeout_opt pre post apply st then
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

fun do_named_method name timeout_opt st =
  do_generic timeout_opt name (#goal o Proof.goal) snd
             (apply_named_method name (Proof.context_of st)) st

fun apply_named_method_on_first_goal name ctxt =
  let val thy = ProofContext.theory_of ctxt in
    Proof.refine (Method.SelectGoals (1, Method.Basic (named_method thy name)))
  end

fun do_named_method (name, all_goals) timeout_opt st =
  do_generic timeout_opt
             (name ^ (if all_goals andalso
                         nprems_of (#goal (Proof.goal st)) > 1 then
                        "[1]"
                      else
                        "")) I (#goal o Proof.goal)
             (apply_named_method_on_first_goal name (Proof.context_of st)) st

val named_methods =
  [("simp", false), ("auto", true), ("fast", false), ("fastsimp", false),
   ("force", false), ("blast", false), ("arith", false)]
val do_methods = map do_named_method named_methods

fun time_string (s, ms) = s ^ ": " ^ string_of_int ms ^ " ms"

fun do_try auto timeout_opt st =
  case do_methods |> Par_List.map (fn f => f timeout_opt st)
                  |> map_filter I |> sort (int_ord o pairself snd) of
    [] => (if auto then () else writeln "No proof found."; (false, st))
  | xs as (s, _) :: _ =>
    let
      val xs = xs |> map swap |> AList.coalesce (op =)
                  |> map (swap o apsnd commas)
      val message =
        (if auto then "Auto Try found a proof" else "Try this command") ^ ": " ^
        Markup.markup Markup.sendback
            ((if nprems_of (#goal (Proof.goal st)) = 1 then "by" else "apply") ^
             " " ^ s) ^
        ".\n(" ^ space_implode "; " (map time_string xs) ^ ")\n"
    in
      (true, st |> (if auto then
                      Proof.goal_message
                          (fn () => Pretty.chunks [Pretty.str "",
                                    Pretty.markup Markup.hilite
                                                  [Pretty.str message]])
                    else
                      tap (fn _ => priority message)))
    end

val invoke_try = fst oo do_try false

val tryN = "try"

val _ =
  Outer_Syntax.improper_command tryN
      "try a combination of proof methods" Keyword.diag
      (Scan.succeed (Toplevel.keep (K () o do_try false (SOME default_timeout)
                                    o Toplevel.proof_of)))

fun auto_try st = if not (!auto) then (false, st) else do_try true NONE st

val setup = Auto_Tools.register_tool (tryN, auto_try)

end;
