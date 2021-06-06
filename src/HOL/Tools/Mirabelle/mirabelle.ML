(*  Title:      HOL/Mirabelle/Tools/mirabelle.ML
    Author:     Jasmin Blanchette and Sascha Boehme, TU Munich
    Author:     Makarius
*)

signature MIRABELLE =
sig
  (*core*)
  val print_name: string -> string
  val print_properties: Properties.T -> string
  type context =
    {index: int, tag: string, arguments: Properties.T, timeout: Time.time, theory: theory}
  type command = {name: string, pos: Position.T, pre: Proof.state, post: Toplevel.state}
  val theory_action: binding -> (context -> command list -> XML.body) -> theory -> theory
  val log_command: command -> XML.body -> XML.tree
  val log_report: Properties.T -> XML.body -> XML.tree
  val print_exn: exn -> string
  val command_action: binding -> (context -> command -> string) -> theory -> theory

  (*utility functions*)
  val can_apply : Time.time -> (Proof.context -> int -> tactic) ->
    Proof.state -> bool
  val theorems_in_proof_term : theory -> thm -> thm list
  val theorems_of_sucessful_proof: Toplevel.state -> thm list
  val get_argument : (string * string) list -> string * string -> string
  val get_int_argument : (string * string) list -> string * int -> int
  val get_bool_argument : (string * string) list -> string * bool -> bool
  val cpu_time : ('a -> 'b) -> 'a -> 'b * int
end

structure Mirabelle : MIRABELLE =
struct

(** Mirabelle core **)

(* concrete syntax *)

val keywords = Keyword.no_command_keywords (Thy_Header.get_keywords \<^theory>);

val print_name = Token.print_name keywords;
val print_properties = Token.print_properties keywords;

fun read_actions str =
  Token.read_body keywords
    (Parse.enum ";" (Parse.name -- Sledgehammer_Commands.parse_params))
    (Symbol_Pos.explode0 str);


(* actions *)

type command = {name: string, pos: Position.T, pre: Proof.state, post: Toplevel.state};
type context =
  {index: int, tag: string, arguments: Properties.T, timeout: Time.time, theory: theory};

structure Data = Theory_Data
(
  type T = (context -> command list -> XML.body) Name_Space.table;
  val empty = Name_Space.empty_table "mirabelle_action";
  val extend = I;
  val merge = Name_Space.merge_tables;
);

fun theory_action binding action thy =
  let val context = Context.Theory thy |> Name_Space.map_naming (K Name_Space.global_naming);
  in thy |> Data.map (#2 o Name_Space.define context true (binding, action)) end;


(* log content *)

fun log_action name arguments =
  XML.Elem (("action", (Markup.nameN, name) :: arguments),
    [XML.Text (print_name name ^ (if null arguments then "" else " " ^ print_properties arguments))]);

fun log_command ({name, pos, ...}: command) body =
  XML.Elem (("command", (Markup.nameN, name) :: Position.properties_of pos), body);

fun log_report props body =
  XML.Elem (("report", props), body);


(* apply actions *)

fun apply_action index name arguments timeout commands thy =
  let
    val action = #2 (Name_Space.check (Context.Theory thy) (Data.get thy) (name, Position.none));
    val tag = "#" ^ Value.print_int index ^ " " ^ name ^ ": ";
    val context = {index = index, tag = tag, arguments = arguments, timeout = timeout, theory = thy};
    val export_body = action context commands;
    val export_head = log_action name arguments;
    val export_name = Path.binding0 (Path.basic "mirabelle" + Path.basic (Value.print_int index));
  in
    if null export_body then ()
    else Export.export thy export_name (export_head :: export_body)
  end;

fun print_exn exn =
  (case exn of
    Timeout.TIMEOUT _ => "timeout"
  | ERROR msg => "error: " ^ msg
  | exn => "exception:\n" ^ General.exnMessage exn);

fun command_action binding action =
  let
    fun apply context command =
      let val s =
        action context command handle exn =>
          if Exn.is_interrupt exn then Exn.reraise exn
          else #tag context ^ print_exn exn;
      in
        if s = "" then NONE
        else SOME (log_command command [XML.Text s]) end;
  in theory_action binding (map_filter o apply) end;


(* theory line range *)

local

val theory_name =
  Scan.many1 (Symbol_Pos.symbol #> (fn s => Symbol.not_eof s andalso s <> "["))
    >> Symbol_Pos.content;

val line = Symbol_Pos.scan_nat >> (Symbol_Pos.content #> Value.parse_nat);
val end_line = Symbol_Pos.$$ ":" |-- line;
val range = Symbol_Pos.$$ "[" |-- line -- Scan.option end_line --| Symbol_Pos.$$ "]";

in

fun read_theory_range str =
  (case Scan.read Symbol_Pos.stopper (theory_name -- Scan.option range) (Symbol_Pos.explode0 str) of
    SOME res => res
  | NONE => error ("Malformed specification of theory line range: " ^ quote str));

end;

fun check_theories strs =
  let
    val theories = map read_theory_range strs;
    fun get_theory name =
      if null theories then SOME NONE
      else get_first (fn (a, b) => if a = name then SOME b else NONE) theories;
    fun check_line NONE _ = false
      | check_line _ NONE = true
      | check_line (SOME NONE) _ = true
      | check_line (SOME (SOME (line, NONE))) (SOME i) = line <= i
      | check_line (SOME (SOME (line, SOME end_line))) (SOME i) = line <= i andalso i <= end_line;
    fun check_pos range = check_line range o Position.line_of;
  in check_pos o get_theory end;

fun check_session qualifier thy_name (_: Position.T) =
  Resources.theory_qualifier thy_name = qualifier;


(* presentation hook *)

val whitelist = ["apply", "by", "proof"];

val _ =
  Build.add_hook (fn qualifier => fn loaded_theories =>
    let
      val mirabelle_timeout = Options.default_seconds \<^system_option>\<open>mirabelle_timeout\<close>;
      val mirabelle_stride = Options.default_int \<^system_option>\<open>mirabelle_stride\<close>;
      val mirabelle_actions = Options.default_string \<^system_option>\<open>mirabelle_actions\<close>;
      val mirabelle_theories = Options.default_string \<^system_option>\<open>mirabelle_theories\<close>;

      val actions =
        (case read_actions mirabelle_actions of
          SOME actions => actions
        | NONE => error ("Failed to parse mirabelle_actions: " ^ quote mirabelle_actions));
      val check =
        if mirabelle_theories = "" then check_session qualifier
        else check_theories (space_explode "," mirabelle_theories);

      fun theory_commands (thy, segments) =
        let
          val commands = segments
            |> map_index (fn (n, {command = tr, prev_state = st, state = st', ...}) =>
              if n mod mirabelle_stride = 0 then
                let
                  val name = Toplevel.name_of tr;
                  val pos = Toplevel.pos_of tr;
                in
                  if can (Proof.assert_backward o Toplevel.proof_of) st andalso
                    member (op =) whitelist name andalso
                    check (Context.theory_long_name thy) pos
                  then SOME {name = name, pos = pos, pre = Toplevel.proof_of st, post = st'}
                  else NONE
                end
              else NONE)
            |> map_filter I;
        in if null commands then NONE else SOME (thy, commands) end;

      fun app_actions (thy, commands) =
        (actions, ()) |-> fold_index (fn (index, (name, arguments)) => fn () =>
          apply_action (index + 1) name arguments mirabelle_timeout commands thy);
    in
      if null actions then ()
      else List.app app_actions (map_filter theory_commands loaded_theories)
    end);


(* Mirabelle utility functions *)

fun can_apply time tac st =
  let
    val {context = ctxt, facts, goal} = Proof.goal st;
    val full_tac = HEADGOAL (Method.insert_tac ctxt facts THEN' tac ctxt);
  in
    (case try (Timeout.apply time (Seq.pull o full_tac)) goal of
      SOME (SOME _) => true
    | _ => false)
  end;

local

fun fold_body_thms f =
  let
    fun app n (PBody {thms, ...}) = thms |> fold (fn (i, thm_node) =>
      fn (x, seen) =>
        if Inttab.defined seen i then (x, seen)
        else
          let
            val name = Proofterm.thm_node_name thm_node;
            val prop = Proofterm.thm_node_prop thm_node;
            val body = Future.join (Proofterm.thm_node_body thm_node);
            val (x', seen') =
              app (n + (if name = "" then 0 else 1)) body
                (x, Inttab.update (i, ()) seen);
        in (x' |> n = 0 ? f (name, prop, body), seen') end);
  in fn bodies => fn x => #1 (fold (app 0) bodies (x, Inttab.empty)) end;

in

fun theorems_in_proof_term thy thm =
  let
    val all_thms = Global_Theory.all_thms_of thy true;
    fun collect (s, _, _) = if s <> "" then insert (op =) s else I;
    fun member_of xs (x, y) = if member (op =) xs x then SOME y else NONE;
    fun resolve_thms names = map_filter (member_of names) all_thms;
  in resolve_thms (fold_body_thms collect [Thm.proof_body_of thm] []) end;

end;

fun theorems_of_sucessful_proof st =
  (case try Toplevel.proof_of st of
    NONE => []
  | SOME prf => theorems_in_proof_term (Proof.theory_of prf) (#goal (Proof.goal prf)));

fun get_argument arguments (key, default) =
  the_default default (AList.lookup (op =) arguments key);

fun get_int_argument arguments (key, default) =
  (case Option.map Int.fromString (AList.lookup (op =) arguments key) of
    SOME (SOME i) => i
  | SOME NONE => error ("bad option: " ^ key)
  | NONE => default);

fun get_bool_argument arguments (key, default) =
  (case Option.map Bool.fromString (AList.lookup (op =) arguments key) of
    SOME (SOME i) => i
  | SOME NONE => error ("bad option: " ^ key)
  | NONE => default);

fun cpu_time f x =
  let val ({cpu, ...}, y) = Timing.timing f x
  in (y, Time.toMilliseconds cpu) end;

end
