(* Title:      HOL/Tools/try0.ML
   Author:     Jasmin Blanchette, LMU Muenchen
   Author:     Martin Desharnais, LMU Muenchen
   Author:     Fabian Huch, TU Muenchen

Try a combination of proof methods.
*)

signature TRY0 =
sig
  val serial_commas : string -> string list -> string list

  type xref = Facts.ref * Token.src list

  type facts =
    {usings: xref list,
     simps : xref list,
     intros : xref list,
     elims : xref list,
     dests : xref list}
  val empty_facts : facts

  type result = {name: string, command: string, time: Time.time, state: Proof.state}
  type proof_method = Time.time option -> facts -> Proof.state -> result option
  type proof_method_options = {run_if_auto_try: bool}

  val register_proof_method : string -> proof_method_options -> proof_method -> unit
  val get_proof_method : string -> proof_method option
  val get_proof_method_or_noop : string -> proof_method
  val get_all_proof_method_names : unit -> string list

  val schedule : string Config.T

  datatype mode = Auto_Try | Try | Normal
  val generic_try0 : mode -> Time.time option -> facts -> Proof.state ->
    (bool * (string * string list)) * result list
  val try0 : Time.time option -> facts -> Proof.state -> result list
end

structure Try0 : TRY0 =
struct

fun serial_commas _ [] = ["??"]
  | serial_commas _ [s] = [s]
  | serial_commas conj [s1, s2] = [s1, conj, s2]
  | serial_commas conj [s1, s2, s3] = [s1 ^ ",", s2 ^ ",", conj, s3]
  | serial_commas conj (s :: ss) = s ^ "," :: serial_commas conj ss;

val noneN = "none"

datatype mode = Auto_Try | Try | Normal

val default_timeout = seconds 5.0

datatype modifier = Use | Simp | Intro | Elim | Dest
type xref = Facts.ref * Token.src list
type tagged_xref = xref * modifier list
type facts =
  {usings: xref list,
   simps : xref list,
   intros : xref list,
   elims : xref list,
   dests : xref list}

val empty_facts: facts = {usings = [], simps = [], intros = [], elims = [], dests = []}
fun union_facts (left : facts) (right : facts) : facts =
  {usings = #usings left @ #usings right,
   simps = #simps left @ #simps right,
   intros = #intros left @ #intros right,
   elims = #elims left @ #elims right,
   dests = #dests left @ #dests right}

type result = {name: string, command: string, time: Time.time, state: Proof.state}
type proof_method = Time.time option -> facts -> Proof.state -> result option
type proof_method_options = {run_if_auto_try: bool}

val noop_proof_method : proof_method = fn _ => fn _ => fn _ => NONE

local
  val proof_methods =
    Synchronized.var "Try0.proof_methods" (Symtab.empty : proof_method Symtab.table);
  val auto_try_proof_methods_names =
    Synchronized.var "Try0.auto_try_proof_methods" (Symset.empty : Symset.T);
in

fun register_proof_method name ({run_if_auto_try} : proof_method_options) proof_method =
  let
    val () = if name = "" then error "Registering unnamed proof method" else ()
    val () = Synchronized.change proof_methods (Symtab.update (name, proof_method))
    val () =
      if run_if_auto_try then
        Synchronized.change auto_try_proof_methods_names (Symset.insert name)
      else
        ()
  in () end

fun get_proof_method (name : string) : proof_method option =
  Symtab.lookup (Synchronized.value proof_methods) name;

fun get_all_proof_method_names () : string list =
  Symtab.fold (fn (name, _) => fn names => name :: names) (Synchronized.value proof_methods) []

fun should_auto_try_proof_method (name : string) : bool =
  Symset.member (Synchronized.value auto_try_proof_methods_names) name

end

fun get_proof_method_or_noop name =
  (case get_proof_method name of
    NONE => (warning ("Proof method \"" ^ name ^ "\" is undefined"); noop_proof_method)
  | SOME proof_method => proof_method)

fun maybe_apply_proof_method name mode : proof_method =
  if mode <> Auto_Try orelse should_auto_try_proof_method name then
    get_proof_method_or_noop name
  else
    noop_proof_method

val schedule = Attrib.setup_config_string \<^binding>\<open>try0_schedule\<close> (K "")

local

fun time_string time = string_of_int (Time.toMilliseconds time) ^ " ms"
fun tool_time_string (s, time) = s ^ ": " ^ time_string time

fun generic_try0_step mode (timeout_opt : Time.time option) (facts : facts) (st : Proof.state)
  (proof_methods : string list) =
  let
    fun try_method (method : mode -> proof_method) = method mode timeout_opt facts st
    fun get_message {command, time, ...} = "Found proof: " ^ Active.sendback_markup_command
      command ^ " (" ^ time_string time ^ ")"
    val print_step = Option.map (tap (writeln o get_message))
    fun get_results methods : result list =
      if mode = Normal then
        methods
        |> Par_List.map (try_method #> print_step)
        |> map_filter I
        |> sort (Time.compare o apply2 #time)
      else
        methods
        |> Par_List.get_some try_method
        |> the_list
    val maybe_apply_methods = map maybe_apply_proof_method proof_methods
  in
    if mode = Normal then
      let val names = map quote proof_methods in
        writeln ("Trying " ^ implode_space (serial_commas "and" names) ^ "...")
      end
    else
      ();
    (case get_results maybe_apply_methods of
      [] => (if mode = Normal then writeln "No proof found" else (); ((false, (noneN, [])), []))
    | results as {name, command, ...} :: _ =>
      let
        val method_times =
          results
          |> map (fn {name, time, ...} => (time, name))
          |> AList.coalesce (op =)
          |> map (swap o apsnd commas)
        val message =
          (case mode of
             Auto_Try => "Auto Try0 found a proof"
           | Try => "Try0 found a proof"
           | Normal => "Try this") ^ ": " ^
          Active.sendback_markup_command command ^
          (case method_times of
            [(_, ms)] => " (" ^ time_string ms ^ ")"
          | method_times => "\n(" ^ space_implode "; " (map tool_time_string method_times) ^ ")")
      in
        ((true, (name, if mode = Auto_Try then [message] else (writeln message; []))), results)
      end)
  end

in

fun generic_try0 mode (timeout_opt : Time.time option) (facts : facts) (st : Proof.state) =
  let
    fun some_nonempty_string sub =
      if Substring.isEmpty sub then
        NONE
      else
        SOME (Substring.string sub)
    val schedule =
      Config.get (Proof.context_of st) schedule
      |> Substring.full
      |> Substring.tokens (fn c => c = #"|")
      |> map (map_filter some_nonempty_string o Substring.tokens Char.isSpace)
    fun iterate [] = ((false, (noneN, [])), [])
      | iterate (proof_methods :: proof_methodss) =
        (case generic_try0_step mode timeout_opt facts st proof_methods of
          (_, []) => iterate proof_methodss
        | result as (_, _ :: _) => result)
  in
    iterate (if null schedule then [get_all_proof_method_names ()] else schedule)
  end;

end

fun try0 timeout_opt = snd oo generic_try0 Normal timeout_opt

fun try0_trans (facts : facts) =
  Toplevel.keep_proof (ignore o try0 (SOME default_timeout) facts o Toplevel.proof_of)

val parse_fact_refs = Scan.repeat1 (Scan.unless (Parse.name -- Args.colon) Parse.thm)

val parse_attr =
  Args.$$$ "simp" |-- Args.colon |-- parse_fact_refs >> (fn xrefs =>
    {usings = [], simps = xrefs, intros = [], elims = [], dests = []})
  || Args.$$$ "intro" |-- Args.colon |-- parse_fact_refs >> (fn xrefs =>
    {usings = [], simps = [], intros = xrefs, elims = [], dests = []})
  || Args.$$$ "elim" |-- Args.colon |-- parse_fact_refs >> (fn xrefs =>
    {usings = [], simps = [], intros = [], elims = xrefs, dests = []})
  || Args.$$$ "dest" |-- Args.colon |-- parse_fact_refs >> (fn xrefs =>
    {usings = [], simps = [], intros = [], elims = [], dests = xrefs})

fun parse_attrs x =
  (Args.parens parse_attrs
   || Scan.repeat parse_attr >> (fn factss => fold union_facts factss empty_facts)) x

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>try0\<close> "try a combination of proof methods"
    (Scan.optional parse_attrs empty_facts #>> try0_trans)

end
