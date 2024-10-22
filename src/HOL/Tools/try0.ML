(*  Title:      HOL/Tools/try0.ML
    Author:     Jasmin Blanchette, TU Muenchen

Try a combination of proof methods.
*)

signature TRY0 =
sig
  val noneN : string
  val silence_methods : bool -> Proof.context -> Proof.context
  type result = {name: string, command: string, time: int, state: Proof.state}
  val try0 : Time.time option -> string list * string list * string list * string list ->
    Proof.state -> result list
end;

structure Try0 : TRY0 =
struct

val noneN = "none";

datatype mode = Auto_Try | Try | Normal;

val default_timeout = seconds 5.0;

fun run_tac timeout_opt tac st =
  let val with_timeout =
    (case timeout_opt of SOME timeout => Timeout.apply_physical timeout | NONE => I)
  in with_timeout (Seq.pull o tac) st |> Option.map fst end;

fun apply_recursive recurse elapsed0 timeout_opt post apply st =
  (case Timing.timing (Option.join o try (run_tac timeout_opt apply)) st of
    ({elapsed, ...}, SOME st') =>
      if recurse andalso (st' |> Thm.nprems_of o #goal o Proof.goal) > 0 then
        let val timeout_opt1 = (Option.map (fn timeout => timeout - elapsed) timeout_opt)
        in apply_recursive recurse (elapsed0 + elapsed) timeout_opt1 post apply st' end
      else (elapsed0 + elapsed, st')
   |_ => (elapsed0, st))

fun parse_method ctxt s =
  enclose "(" ")" s
  |> Token.explode (Thy_Header.get_keywords' ctxt) Position.start
  |> filter Token.is_proper
  |> Scan.read Token.stopper Method.parse
  |> (fn SOME (Method.Source src, _) => src | _ => raise Fail "expected Source");

fun add_attr_text (NONE, _) s = s
  | add_attr_text (_, []) s = s
  | add_attr_text (SOME x, fs) s =
    s ^ " " ^ (if x = "" then "" else x ^ ": ") ^ implode_space fs;

fun attrs_text (sx, ix, ex, dx) (ss, is, es, ds) =
  "" |> fold add_attr_text [(sx, ss), (ix, is), (ex, es), (dx, ds)];

type result = {name: string, command: string, time: int, state: Proof.state}

fun apply_named_method (name, ((all_goals, run_if_auto_try), attrs)) mode timeout_opt quad st =
  if mode <> Auto_Try orelse run_if_auto_try then
    let
      val attrs = attrs_text attrs quad
      val ctxt = Proof.context_of st

      val apply = name ^ attrs
      |> parse_method ctxt
      |> Method.method_cmd ctxt
      |> Method.Basic
      |> (fn m => Method.Combinator (Method.no_combinator_info, Method.Select_Goals 1, [m]))
      |> Proof.refine
      #> Seq.filter_results

      val the_goal = #goal o Proof.goal
      val num_before = Thm.nprems_of (the_goal st)
      val multiple_goals = all_goals andalso num_before > 1
      val (time, st') = apply_recursive multiple_goals Time.zeroTime timeout_opt the_goal apply st
      val num_after = Thm.nprems_of (the_goal st')
      val select = "[" ^ string_of_int (num_before - num_after)  ^ "]"
      val command =
        (if num_after = 0 then "by " else "apply ") ^
        (name ^ attrs |> attrs <> "" ? enclose "(" ")") ^
        (if multiple_goals andalso num_after > 0 then select else "")
    in
      if num_before > num_after then
        SOME {name = name, command = command, time = Time.toMilliseconds time, state = st'}
      else NONE
    end
  else NONE;

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
   ("argo", ((false, true), no_attrs)),
   ("linarith", ((false, true), no_attrs)),
   ("presburger", ((false, true), no_attrs)),
   ("algebra", ((false, true), no_attrs)),
   ("fast", ((false, false), clas_attrs)),
   ("fastforce", ((false, false), full_attrs)),
   ("force", ((false, false), full_attrs)),
   ("meson", ((false, false), metis_attrs)),
   ("satx", ((false, false), no_attrs)),
   ("order", ((false, true), no_attrs))];

val apply_methods = map apply_named_method named_methods;

fun time_string ms = string_of_int ms ^ " ms";
fun tool_time_string (s, ms) = s ^ ": " ^ time_string ms;

(* Makes reconstructor tools as silent as possible. The "set_visible" calls suppresses "Unification
   bound exceeded" warnings and the like. *)
fun silence_methods debug =
  Config.put Metis_Tactic.verbose debug
  #> not debug ? (fn ctxt =>
      ctxt
      |> Simplifier_Trace.disable
      |> Context_Position.set_visible false
      |> Config.put Unify.unify_trace false
      |> Config.put Argo_Tactic.trace "none"
      |> Proof_Context.background_theory (fn thy =>
          thy
          |> Context_Position.set_visible_global false
          |> Config.put_global Unify.unify_trace false));

fun generic_try0 mode timeout_opt quad st =
  let
    val st = Proof.map_contexts (silence_methods false) st;
    fun try_method method = method mode timeout_opt quad st;
    fun get_message {command, time, ...} = "Found proof: " ^ Active.sendback_markup_command
      command ^ " (" ^ time_string time ^ ")";
    val print_step = Option.map (tap (writeln o get_message));
    val get_results =
      if mode = Normal
      then Par_List.map (try_method #> print_step) #> map_filter I #> sort (int_ord o apply2 #time)
      else Par_List.get_some try_method #> the_list;
  in
    if mode = Normal then
      "Trying " ^ implode_space (Try.serial_commas "and" (map (quote o fst) named_methods)) ^
      "..."
      |> writeln
    else
      ();
    (case get_results apply_methods of
      [] => (if mode = Normal then writeln "No proof found" else (); ((false, (noneN, [])), []))
    | results as {name, command, ...} :: _ =>
      let
        val method_times =
          results
          |> map (fn {name, time, ...} => (time, name))
          |> AList.coalesce (op =)
          |> map (swap o apsnd commas);
        val message =
          (case mode of
             Auto_Try => "Auto Try0 found a proof"
           | Try => "Try0 found a proof"
           | Normal => "Try this") ^ ": " ^
          Active.sendback_markup_command command ^
          (case method_times of
            [(_, ms)] => " (" ^ time_string ms ^ ")"
          | method_times => "\n(" ^ space_implode "; " (map tool_time_string method_times) ^ ")");
      in
        ((true, (name, if mode = Auto_Try then [message] else (writeln message; []))), results)
      end)
  end;

fun try0 timeout_opt = snd oo generic_try0 Normal timeout_opt;

fun try0_trans quad =
  Toplevel.keep_proof
    (ignore o generic_try0 Normal (SOME default_timeout) quad o Toplevel.proof_of);

fun merge_attrs (s1, i1, e1, d1) (s2, i2, e2, d2) = (s1 @ s2, i1 @ i2, e1 @ e2, d1 @ d2);

fun string_of_xthm (xref, args) =
  Facts.string_of_ref xref ^
  implode (map (enclose "[" "]" o Pretty.unformatted_string_of o Token.pretty_src \<^context>) args);

val parse_fact_refs =
  Scan.repeat1 (Scan.unless (Parse.name -- Args.colon) (Parse.thm >> string_of_xthm));

val parse_attr =
  Args.$$$ "simp" |-- Args.colon |-- parse_fact_refs >> (fn ss => (ss, [], [], []))
  || Args.$$$ "intro" |-- Args.colon |-- parse_fact_refs >> (fn is => ([], is, [], []))
  || Args.$$$ "elim" |-- Args.colon |-- parse_fact_refs >> (fn es => ([], [], es, []))
  || Args.$$$ "dest" |-- Args.colon |-- parse_fact_refs >> (fn ds => ([], [], [], ds));

fun parse_attrs x =
  (Args.parens parse_attrs
   || Scan.repeat parse_attr >> (fn quad => fold merge_attrs quad ([], [], [], []))) x;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>try0\<close> "try a combination of proof methods"
    (Scan.optional parse_attrs ([], [], [], []) #>> try0_trans);

val _ =
  Try.tool_setup
   {name = "try0", weight = 30, auto_option = \<^system_option>\<open>auto_methods\<close>,
    body = fn auto => fst o generic_try0 (if auto then Auto_Try else Try) NONE ([], [], [], [])};

end;
