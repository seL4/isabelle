(*  Title:      HOL/Tools/try.ML
    Author:     Jasmin Blanchette, TU Muenchen

Try a combination of proof methods.
*)

signature TRY =
sig
  val auto : bool Unsynchronized.ref
  val invoke_try :
    Time.time option -> string list * string list * string list * string list
    -> Proof.state -> bool
  val setup : theory -> theory
end;

structure Try : TRY =
struct

val auto = Unsynchronized.ref false

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
      (Preferences.bool_pref auto "auto-try" "Try standard proof methods.")

val default_timeout = seconds 5.0

fun can_apply timeout_opt pre post tac st =
  let val {goal, ...} = Proof.goal st in
    case (case timeout_opt of
            SOME timeout => TimeLimit.timeLimit timeout
          | NONE => fn f => fn x => f x) (Seq.pull o tac) (pre st) of
      SOME (x, _) => nprems_of (post x) < nprems_of goal
    | NONE => false
  end
  handle TimeLimit.TimeOut => false

fun do_generic timeout_opt command pre post apply st =
  let val timer = Timer.startRealTimer () in
    if can_apply timeout_opt pre post apply st then
      SOME (command, Time.toMilliseconds (Timer.checkRealTimer timer))
    else
      NONE
  end

val parse_method =
  enclose "(" ")"
  #> Outer_Syntax.scan Position.start
  #> filter Token.is_proper
  #> Scan.read Token.stopper Method.parse
  #> (fn SOME (Method.Source src) => src | _ => raise Fail "expected Source")

fun apply_named_method_on_first_goal method thy =
  method |> parse_method
         |> Method.method thy
         |> Method.Basic
         |> curry Method.SelectGoals 1
         |> Proof.refine
  handle ERROR _ => K Seq.empty (* e.g., the method isn't available yet *)

fun add_attr_text (NONE, _) s = s
  | add_attr_text (_, []) s = s
  | add_attr_text (SOME x, fs) s =
    s ^ " " ^ (if x = "" then "" else x ^ ": ") ^ space_implode " " fs
fun attrs_text (sx, ix, ex, dx) (ss, is, es, ds) =
  "" |> fold add_attr_text [(sx, ss), (ix, is), (ex, es), (dx, ds)]

fun do_named_method (name, ((all_goals, run_if_auto), attrs)) auto timeout_opt
                    quad st =
  if not auto orelse run_if_auto then
    let val attrs = attrs_text attrs quad in
      do_generic timeout_opt
                 (name ^ (if all_goals andalso
                             nprems_of (#goal (Proof.goal st)) > 1 then
                            "[1]"
                          else
                            "") ^
                  attrs) I (#goal o Proof.goal)
                 (apply_named_method_on_first_goal (name ^ attrs)
                                                   (Proof.theory_of st)) st
    end
  else
    NONE

val full_attrs = (SOME "simp", SOME "intro", SOME "elim", SOME "dest")
val clas_attrs = (NONE, SOME "intro", SOME "elim", SOME "dest")
val simp_attrs = (SOME "add", NONE, NONE, NONE)
val metis_attrs = (SOME "", SOME "", SOME "", SOME "")
val no_attrs = (NONE, NONE, NONE, NONE)

(* name * ((all_goals, run_if_auto), (simp, intro, elim, dest) *)
val named_methods =
  [("simp", ((false, true), simp_attrs)),
   ("auto", ((true, true), full_attrs)),
   ("fast", ((false, false), clas_attrs)),
   ("fastsimp", ((false, false), full_attrs)),
   ("force", ((false, false), full_attrs)),
   ("blast", ((false, true), clas_attrs)),
   ("metis", ((false, true), metis_attrs)),
   ("linarith", ((false, true), no_attrs)),
   ("presburger", ((false, true), no_attrs))]
val do_methods = map do_named_method named_methods

fun time_string (s, ms) = s ^ ": " ^ string_of_int ms ^ " ms"

fun do_try auto timeout_opt quad st =
  let
    val st = st |> Proof.map_context (Config.put Metis_Tactics.verbose false)
  in
    case do_methods |> Par_List.map (fn f => f auto timeout_opt quad st)
                    |> map_filter I |> sort (int_ord o pairself snd) of
      [] => (if auto then () else writeln "No proof found."; (false, st))
    | xs as (s, _) :: _ =>
      let
        val xs = xs |> map (fn (s, n) => (n, hd (space_explode " " s)))
                    |> AList.coalesce (op =)
                    |> map (swap o apsnd commas)
        val need_parens = exists_string (curry (op =) " ") s
        val message =
          (if auto then "Auto Try found a proof" else "Try this command") ^
          ": " ^
          Markup.markup Markup.sendback
              ((if nprems_of (#goal (Proof.goal st)) = 1 then "by"
                else "apply") ^ " " ^ (s |> need_parens ? enclose "(" ")")) ^
          "\n(" ^ space_implode "; " (map time_string xs) ^ ").\n"
      in
        (true, st |> (if auto then
                        Proof.goal_message
                            (fn () => Pretty.chunks [Pretty.str "",
                                      Pretty.markup Markup.hilite
                                                    [Pretty.str message]])
                      else
                        tap (fn _ => Output.urgent_message message)))
      end
  end

fun invoke_try timeout_opt = fst oo do_try false timeout_opt

val tryN = "try"

fun try_trans quad =
  Toplevel.keep (K () o do_try false (SOME default_timeout) quad
                 o Toplevel.proof_of)

fun merge_attrs (s1, i1, e1, d1) (s2, i2, e2, d2) =
  (s1 @ s2, i1 @ i2, e1 @ e2, d1 @ d2)

fun string_of_xthm (xref, args) =
  Facts.string_of_ref xref ^
  implode (map (enclose "[" "]" o Pretty.str_of
                o Args.pretty_src @{context}) args)

val parse_fact_refs =
  Scan.repeat1 (Scan.unless (Parse.name -- Args.colon)
                            (Parse_Spec.xthm >> string_of_xthm))
val parse_attr =
     Args.$$$ "simp" |-- Args.colon |-- parse_fact_refs
     >> (fn ss => (ss, [], [], []))
  || Args.$$$ "intro" |-- Args.colon |-- parse_fact_refs
     >> (fn is => ([], is, [], []))
  || Args.$$$ "elim" |-- Args.colon |-- parse_fact_refs
     >> (fn es => ([], [], es, []))
  || Args.$$$ "dest" |-- Args.colon |-- parse_fact_refs
     >> (fn ds => ([], [], [], ds))
fun parse_attrs x =
    (Args.parens parse_attrs
  || Scan.repeat parse_attr
     >> (fn quad => fold merge_attrs quad ([], [], [], []))) x

val parse_try_command = Scan.optional parse_attrs ([], [], [], []) #>> try_trans

val _ =
  Outer_Syntax.improper_command tryN
      "try a combination of proof methods" Keyword.diag parse_try_command

val auto_try = do_try true NONE ([], [], [], [])

val setup = Auto_Tools.register_tool (auto, auto_try)

end;
