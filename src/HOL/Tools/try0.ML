(*  Title:      HOL/Tools/try0.ML
    Author:     Jasmin Blanchette, TU Muenchen

Try a combination of proof methods.
*)

signature TRY0 =
sig
  val try0N : string
  val noneN : string

  val silence_methods : bool -> Proof.context -> Proof.context
  val try0 : Time.time option -> string list * string list * string list * string list ->
    Proof.state -> bool
end;

structure Try0 : TRY0 =
struct

val try0N = "try0";
val noneN = "none";

datatype mode = Auto_Try | Try | Normal;

val _ =
  ProofGeneral.preference_option ProofGeneral.category_tracing
    NONE
    @{option auto_methods}
    "auto-try0"
    "Try standard proof methods";

val default_timeout = seconds 5.0;

fun can_apply timeout_opt pre post tac st =
  let val {goal, ...} = Proof.goal st in
    case (case timeout_opt of
            SOME timeout => TimeLimit.timeLimit timeout
          | NONE => fn f => fn x => f x) (Seq.pull o tac) (pre st) of
      SOME (x, _) => nprems_of (post x) < nprems_of goal
    | NONE => false
  end
  handle TimeLimit.TimeOut => false;

fun apply_generic timeout_opt name command pre post apply st =
  let val timer = Timer.startRealTimer () in
    if can_apply timeout_opt pre post apply st then
      SOME (name, command, Time.toMilliseconds (Timer.checkRealTimer timer))
    else
      NONE
  end;

val parse_method =
  enclose "(" ")"
  #> Outer_Syntax.scan Position.start
  #> filter Token.is_proper
  #> Scan.read Token.stopper Method.parse
  #> (fn SOME (Method.Source src, _) => src | _ => raise Fail "expected Source");

fun apply_named_method_on_first_goal thy method =
  method
  |> parse_method
  |> Method.method thy
  |> Method.Basic
  |> curry Method.Select_Goals 1
  |> Proof.refine
  handle ERROR _ => K Seq.empty; (* e.g., the method isn't available yet *)

fun add_attr_text (NONE, _) s = s
  | add_attr_text (_, []) s = s
  | add_attr_text (SOME x, fs) s =
    s ^ " " ^ (if x = "" then "" else x ^ ": ") ^ space_implode " " fs;

fun attrs_text (sx, ix, ex, dx) (ss, is, es, ds) =
  "" |> fold add_attr_text [(sx, ss), (ix, is), (ex, es), (dx, ds)];

fun apply_named_method (name, ((all_goals, run_if_auto_try), attrs)) mode timeout_opt quad st =
  if mode <> Auto_Try orelse run_if_auto_try then
    let val attrs = attrs_text attrs quad in
      apply_generic timeout_opt name
        ((name ^ attrs |> attrs <> "" ? enclose "(" ")") ^
         (if all_goals andalso nprems_of (#goal (Proof.goal st)) > 1 then "[1]" else ""))
        I (#goal o Proof.goal)
        (apply_named_method_on_first_goal (Proof.theory_of st) (name ^ attrs)) st
    end
  else
    NONE;

val full_attrs = (SOME "simp", SOME "intro", SOME "elim", SOME "dest");
val clas_attrs = (NONE, SOME "intro", SOME "elim", SOME "dest");
val simp_attrs = (SOME "add", NONE, NONE, NONE);
val metis_attrs = (SOME "", SOME "", SOME "", SOME "");
val no_attrs = (NONE, NONE, NONE, NONE);

(* name * ((all_goals, run_if_auto_try), (simp, intro, elim, dest) *)
val named_methods =
  [("simp", ((false, true), simp_attrs)),
   ("auto", ((true, true), full_attrs)),
   ("blast", ((false, true), clas_attrs)),
   ("metis", ((false, true), metis_attrs)),
   ("linarith", ((false, true), no_attrs)),
   ("presburger", ((false, true), no_attrs)),
   ("algebra", ((false, true), no_attrs)),
   ("fast", ((false, false), clas_attrs)),
   ("fastforce", ((false, false), full_attrs)),
   ("force", ((false, false), full_attrs)),
   ("meson", ((false, false), metis_attrs))]

val apply_methods = map apply_named_method named_methods;

fun time_string ms = string_of_int ms ^ " ms";
fun tool_time_string (s, ms) = s ^ ": " ^ time_string ms;

(* Makes reconstructor tools as silent as possible. The "set_visible" calls suppresses "Unification
   bound exceeded" warnings and the like. *)
fun silence_methods debug =
  Config.put Metis_Tactic.verbose debug
  #> Config.put Lin_Arith.verbose debug
  #> (not debug ?
    (Context_Position.set_visible false
     #> Proof_Context.background_theory (fn thy =>
       thy
       |> Context_Position.set_visible_global false
       |> Config.put_global Unify.trace_bound (Config.get_global thy Unify.search_bound))));

fun generic_try0 mode timeout_opt quad st =
  let
    val st = st |> Proof.map_context (silence_methods false);
    fun trd (_, _, t) = t;
    fun par_map f =
      if mode = Normal then Par_List.map f #> map_filter I #> sort (int_ord o pairself trd)
      else Par_List.get_some f #> the_list;
  in
    if mode = Normal then
      "Trying " ^ space_implode " " (Try.serial_commas "and" (map (quote o fst) named_methods)) ^
      "..."
      |> Output.urgent_message
    else
      ();
    (case par_map (fn f => f mode timeout_opt quad st) apply_methods of
      [] =>
      (if mode = Normal then Output.urgent_message "No proof found." else (); (false, (noneN, st)))
    | xs as (name, command, _) :: _ =>
      let
        val xs = xs |> map (fn (name, _, n) => (n, name))
                    |> AList.coalesce (op =)
                    |> map (swap o apsnd commas)
        val message =
          (case mode of
             Auto_Try => "Auto Try0 found a proof"
           | Try => "Try0 found a proof"
           | Normal => "Try this") ^ ": " ^
          Active.sendback_markup [Markup.padding_command]
              ((if nprems_of (#goal (Proof.goal st)) = 1 then "by"
                else "apply") ^ " " ^ command) ^
          (case xs of
            [(_, ms)] => " (" ^ time_string ms ^ ")."
          | xs => "\n(" ^ space_implode "; " (map tool_time_string xs) ^ ").")
      in
        (true, (name,
           st
           |> (if mode = Auto_Try then
                 Proof.goal_message (fn () => Pretty.markup Markup.information [Pretty.str message])
               else
                 tap (fn _ => Output.urgent_message message))))
      end)
  end;

fun try0 timeout_opt = fst oo generic_try0 Normal timeout_opt;

fun try0_trans quad =
  Toplevel.unknown_proof o
  Toplevel.keep (K () o generic_try0 Normal (SOME default_timeout) quad o Toplevel.proof_of);

fun merge_attrs (s1, i1, e1, d1) (s2, i2, e2, d2) = (s1 @ s2, i1 @ i2, e1 @ e2, d1 @ d2);

fun string_of_xthm (xref, args) =
  Facts.string_of_ref xref ^
  implode (map (enclose "[" "]" o Pretty.str_of o Args.pretty_src @{context}) args);

val parse_fact_refs =
  Scan.repeat1 (Scan.unless (Parse.name -- Args.colon) (Parse_Spec.xthm >> string_of_xthm));

val parse_attr =
  Args.$$$ "simp" |-- Args.colon |-- parse_fact_refs >> (fn ss => (ss, [], [], []))
  || Args.$$$ "intro" |-- Args.colon |-- parse_fact_refs >> (fn is => ([], is, [], []))
  || Args.$$$ "elim" |-- Args.colon |-- parse_fact_refs >> (fn es => ([], [], es, []))
  || Args.$$$ "dest" |-- Args.colon |-- parse_fact_refs >> (fn ds => ([], [], [], ds));

fun parse_attrs x =
  (Args.parens parse_attrs
   || Scan.repeat parse_attr >> (fn quad => fold merge_attrs quad ([], [], [], []))) x;

val _ =
  Outer_Syntax.improper_command @{command_spec "try0"} "try a combination of proof methods"
    (Scan.optional parse_attrs ([], [], [], []) #>> try0_trans);

fun try_try0 auto = generic_try0 (if auto then Auto_Try else Try) NONE ([], [], [], []);

val _ = Try.tool_setup (try0N, (30, @{option auto_methods}, try_try0));

end;
