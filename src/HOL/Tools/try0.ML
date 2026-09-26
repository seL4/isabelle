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

  type xxrefs = {usings : xref list, directs : xref list}
  val union_xxrefs : xxrefs -> xxrefs -> xxrefs

  val simpN : string
  val introN : string
  val elimN : string
  val destN : string
  val splitN : string
  val iffN : string
  val congN : string
  val native_classes : string list

  type facts = {unclassified : xxrefs, classified : xxrefs Symtab.table}
  val empty_facts : facts
  val union_facts : facts -> facts -> facts
  val get_class_xxrefs : string -> facts -> xxrefs
  val map_class_xxrefs : string -> (xxrefs -> xxrefs) -> facts -> facts

  type result = {name: string, command: string, time: Time.time, state: Proof.state}
  type proof_method = Time.time option -> facts -> Proof.state -> result option
  type proof_method_options = {run_if_auto_try: bool}

  val register_proof_method : string -> proof_method_options -> proof_method -> unit
  val get_proof_method : Proof.context -> string -> proof_method option
  val get_proof_method_or_noop : Proof.context -> string -> proof_method
  val get_all_proof_method_names : Proof.context -> string list

  type fact_classifier = Proof.context -> facts -> facts
  val register_fact_classifier : string -> fact_classifier -> unit
  val get_fact_classifier : Proof.context -> string -> fact_classifier option
  val fact_classifier : string Config.T
  val classify_facts : Proof.context -> facts -> facts

  val default_timeout : int Config.T
  val schedule : string Config.T
  val get_schedule : Proof.context -> string list list

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

type xref = Facts.ref * Token.src list

type xxrefs = {usings : xref list, directs : xref list}

fun union_xxrefs (left : xxrefs) (right : xxrefs) : xxrefs =
  {usings = #usings left @ #usings right, directs = #directs left @ #directs right}

val simpN = "simp"
val introN = "intro"
val elimN = "elim"
val destN = "dest"
val splitN = "split"
val iffN = "iff"
val congN = "cong"
val native_classes = [simpN, introN, elimN, destN, splitN, iffN, congN]

type facts = {unclassified : xxrefs, classified : xxrefs Symtab.table}

val empty_facts : facts = {unclassified = {usings = [], directs = []}, classified = Symtab.empty}

fun union_facts (left : facts) (right : facts) : facts =
  {unclassified = union_xxrefs (#unclassified left) (#unclassified right),
   classified = Symtab.join (K (uncurry union_xxrefs)) (#classified left, #classified right)}

fun get_class_xxrefs (class : string) ({classified, ...} : facts) : xxrefs =
  the_default {usings = [], directs = []} (Symtab.lookup classified class)

fun map_class_xxrefs (class : string) (f : xxrefs -> xxrefs) (facts : facts) : facts =
  let
    val classified = #classified facts
    val classified' =
      (case f (get_class_xxrefs class facts) of
        {usings = [], directs = []} => Symtab.delete_safe class classified
      | xxrefs => Symtab.update (class, xxrefs) classified)
  in {unclassified = #unclassified facts, classified = classified'} end

type result = {name: string, command: string, time: Time.time, state: Proof.state}
type proof_method = Time.time option -> facts -> Proof.state -> result option
type proof_method_options = {run_if_auto_try: bool}

val noop_proof_method : proof_method = fn _ => fn _ => fn _ => NONE

structure Proof_Method_Data = Generic_Data
(
  type T = (proof_method * proof_method_options) Symtab.table
  val empty = Symtab.empty
  fun merge data = Symtab.merge (K true) data
)

fun register_proof_method (name : string) (options : proof_method_options)
    (proof_method : proof_method) : unit =
  let val () = if name = "" then error "Registering unnamed proof method" else () in
    Context.>> (Proof_Method_Data.map (Symtab.update (name, (proof_method, options))))
  end

fun get_proof_methods (ctxt : Proof.context) : (proof_method * proof_method_options) Symtab.table =
  Proof_Method_Data.get (Context.Proof ctxt)

fun get_proof_method (ctxt : Proof.context) (name : string) : proof_method option =
  Option.map fst (Symtab.lookup (get_proof_methods ctxt) name)

fun get_all_proof_method_names (ctxt : Proof.context) : string list =
  Symtab.fold (fn (name, _) => fn names => name :: names) (get_proof_methods ctxt) []

fun should_auto_try_proof_method (ctxt : Proof.context) (name : string) : bool =
  (case Symtab.lookup (get_proof_methods ctxt) name of
    SOME (_, {run_if_auto_try}) => run_if_auto_try
  | NONE => false)

fun get_proof_method_or_noop (ctxt : Proof.context) (name : string) : proof_method =
  (case get_proof_method ctxt name of
    NONE => (warning ("Proof method \"" ^ name ^ "\" is undefined"); noop_proof_method)
  | SOME proof_method => proof_method)

fun maybe_apply_proof_method (ctxt : Proof.context) (name : string) (mode : mode) : proof_method =
  if mode <> Auto_Try orelse should_auto_try_proof_method ctxt name then
    get_proof_method_or_noop ctxt name
  else
    noop_proof_method

type fact_classifier = Proof.context -> facts -> facts

structure Fact_Classifier_Data = Generic_Data
(
  type T = fact_classifier Symtab.table
  val empty = Symtab.empty
  fun merge data = Symtab.merge (K true) data
)

fun register_fact_classifier (name : string) (classifier : fact_classifier) : unit =
  let val () = if name = "" then error "Registering unnamed fact classifier" else () in
    Context.>> (Fact_Classifier_Data.map (Symtab.update (name, classifier)))
  end

fun get_fact_classifier (ctxt : Proof.context) (name : string) : fact_classifier option =
  Symtab.lookup (Fact_Classifier_Data.get (Context.Proof ctxt)) name;

val fact_classifier =
  Attrib.setup_option_string (\<^system_option>\<open>try0_fact_classifier\<close>, \<^here>)

fun classify_facts (ctxt : Proof.context) (facts : facts) : facts =
  (case Config.get ctxt fact_classifier of
    "" => facts
  | name =>
      (case get_fact_classifier ctxt name of
        NONE => (warning ("Fact classifier \"" ^ name ^ "\" is undefined"); facts)
      | SOME classifier => classifier ctxt facts))

val default_timeout = Attrib.setup_config_int \<^binding>\<open>try0_default_timeout\<close> (K 2)
val schedule = Attrib.setup_config_string \<^binding>\<open>try0_schedule\<close> (K "")

fun get_schedule (ctxt : Proof.context) : string list list =
  let
    fun some_nonempty_string sub =
      if Substring.isEmpty sub then
        NONE
      else
        SOME (Substring.string sub)
  in
    Config.get ctxt schedule
    |> Substring.full
    |> Substring.tokens (fn c => c = #";")
    |> map (map_filter some_nonempty_string o Substring.tokens Char.isSpace)
  end

local

fun time_string time = string_of_int (Time.toMilliseconds time) ^ " ms"
fun tool_time_string (s, time) = s ^ ": " ^ time_string time

fun generic_try0_step mode (timeout : Time.time) (facts : facts) (st : Proof.state)
  (proof_methods : string list) =
  let
    fun try_method (method : mode -> proof_method) = method mode (SOME timeout) facts st
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
    val maybe_apply_methods = map (maybe_apply_proof_method (Proof.context_of st)) proof_methods
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
    val ctxt = Proof.context_of st
    val schedule = get_schedule ctxt
    and facts = classify_facts ctxt facts
    and timeout =
      (case timeout_opt of
        NONE => seconds (Real.fromInt (Config.get ctxt default_timeout))
      | SOME t => t)

    fun iterate [] = ((false, (noneN, [])), [])
      | iterate (proof_methods :: proof_methodss) =
        (case generic_try0_step mode timeout facts st proof_methods of
          (_, []) => iterate proof_methodss
        | result as (_, _ :: _) => result)
  in
    iterate (if null schedule then [get_all_proof_method_names ctxt] else schedule)
  end;

end

fun try0 timeout_opt = snd oo generic_try0 Normal timeout_opt

fun try0_trans (facts : facts) =
  Toplevel.keep_proof (ignore o try0 NONE facts o Toplevel.proof_of)

local

val parse_fact_refs = Scan.repeat1 (Scan.unless (Parse.name -- Args.colon) Parse.thm)

fun class_section (class : string) =
  Args.$$$ class |-- Args.colon |-- parse_fact_refs >> (fn xrefs =>
    map_class_xxrefs class (K {usings = [], directs = xrefs}) empty_facts)

val parse_unclassified_facts =
  parse_fact_refs >> (fn xrefs =>
    {unclassified = {usings = [], directs = xrefs}, classified = Symtab.empty} : facts)

val parse_classified_facts =
  Scan.repeat1 (Scan.first (map class_section native_classes)) >>
    (fn factss => fold union_facts factss empty_facts)

in

val parse_facts =
  Args.parens (parse_unclassified_facts || parse_classified_facts)
  || Scan.optional parse_classified_facts empty_facts

end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>try0\<close> "try a combination of proof methods"
    (parse_facts #>> try0_trans)

end
