(*  Title:      HOL/Tools/try0.ML
    Author:     Jasmin Blanchette, TU Muenchen

Try a combination of proof methods.
*)

signature TRY0 =
sig
  val serial_commas : string -> string list -> string list

  datatype modifier = Use | Simp | Intro | Elim | Dest
  type xref = Facts.ref * Token.src list
  type tagged_xref = xref * modifier list
  type result = {name: string, command: string, time: Time.time, state: Proof.state}
  type proof_method = Time.time option -> tagged_xref list -> Proof.state -> result option
  type proof_method_options = {run_if_auto_try: bool}

  val register_proof_method : string -> proof_method_options -> proof_method -> unit
  val get_proof_method : string -> proof_method option

  datatype mode = Auto_Try | Try | Normal
  val generic_try0 : mode -> Time.time option -> tagged_xref list -> Proof.state ->
    (bool * (string * string list)) * result list
  val try0 : Time.time option -> tagged_xref list -> Proof.state -> result list
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

type result = {name: string, command: string, time: Time.time, state: Proof.state}
type proof_method = Time.time option -> tagged_xref list -> Proof.state -> result option
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
    val () = Synchronized.change proof_methods (Symtab.update_new (name, proof_method))
    val () =
      if run_if_auto_try then
        Synchronized.change auto_try_proof_methods_names (Symset.insert name)
      else
        ()
  in () end

fun get_proof_method (name : string) : proof_method option =
  Symtab.lookup (Synchronized.value proof_methods) name;

fun get_all_proof_methods () : (string * proof_method) list =
  Symtab.fold (fn x => fn xs => x :: xs) (Synchronized.value proof_methods) []

fun get_all_proof_method_names () : string list =
  Symtab.fold (fn (name, _) => fn names => name :: names) (Synchronized.value proof_methods) []

fun get_all_auto_try_proof_method_names () : string list =
  Symset.dest (Synchronized.value auto_try_proof_methods_names)

fun should_auto_try_proof_method (name : string) : bool =
  Symset.member (Synchronized.value auto_try_proof_methods_names) name

end

fun get_proof_method_or_noop name =
  (case get_proof_method name of
    NONE => noop_proof_method
  | SOME proof_method => proof_method)

fun maybe_apply_proof_method name mode : proof_method =
  if mode <> Auto_Try orelse should_auto_try_proof_method name then
    get_proof_method_or_noop name
  else
    noop_proof_method

fun time_string time = string_of_int (Time.toMilliseconds time) ^ " ms"
fun tool_time_string (s, time) = s ^ ": " ^ time_string time

fun generic_try0 mode timeout_opt (tagged : tagged_xref list) st =
  let
    fun try_method method = method mode timeout_opt tagged st
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
    val proof_method_names = get_all_proof_method_names ()
    val maybe_apply_methods = map maybe_apply_proof_method proof_method_names
  in
    if mode = Normal then
      let val names = map quote proof_method_names in
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

fun try0 timeout_opt = snd oo generic_try0 Normal timeout_opt

fun try0_trans tagged =
  Toplevel.keep_proof
    (ignore o generic_try0 Normal (SOME default_timeout) tagged o Toplevel.proof_of)

val parse_fact_refs = Scan.repeat1 (Scan.unless (Parse.name -- Args.colon) Parse.thm)

val parse_attr =
  Args.$$$ "simp" |-- Args.colon |-- parse_fact_refs >> (map (rpair [Simp]))
  || Args.$$$ "intro" |-- Args.colon |-- parse_fact_refs >> (map (rpair [Intro]))
  || Args.$$$ "elim" |-- Args.colon |-- parse_fact_refs >> (map (rpair [Elim]))
  || Args.$$$ "dest" |-- Args.colon |-- parse_fact_refs >> (map (rpair [Dest]))

fun parse_attrs x =
  (Args.parens parse_attrs
   || Scan.repeat parse_attr >> (fn tagged => fold (curry (op @)) tagged [])) x

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>try0\<close> "try a combination of proof methods"
    (Scan.optional parse_attrs [] #>> try0_trans)

end
