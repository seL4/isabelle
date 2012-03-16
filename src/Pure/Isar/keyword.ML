(*  Title:      Pure/Isar/keyword.ML
    Author:     Makarius

Isar command keyword classification and global keyword tables.
*)

signature KEYWORD =
sig
  type T
  val kind_of: T -> string
  val control: T
  val diag: T
  val thy_begin: T
  val thy_switch: T
  val thy_end: T
  val thy_heading: T
  val thy_decl: T
  val thy_script: T
  val thy_goal: T
  val thy_schematic_goal: T
  val qed: T
  val qed_block: T
  val qed_global: T
  val prf_heading: T
  val prf_goal: T
  val prf_block: T
  val prf_open: T
  val prf_close: T
  val prf_chain: T
  val prf_decl: T
  val prf_asm: T
  val prf_asm_goal: T
  val prf_script: T
  val kinds: string list
  val tag: string -> T -> T
  val tags_of: T -> string list
  val tag_theory: T -> T
  val tag_proof: T -> T
  val tag_ml: T -> T
  type spec = string * string list
  val spec: spec -> T
  val command_spec: string * spec -> string * T
  val get_lexicons: unit -> Scan.lexicon * Scan.lexicon
  val is_keyword: string -> bool
  val command_keyword: string -> T option
  val command_tags: string -> string list
  val dest: unit -> string list * string list
  val keyword_statusN: string
  val status: unit -> unit
  val define: string * T option -> unit
  val is_diag: string -> bool
  val is_control: string -> bool
  val is_regular: string -> bool
  val is_heading: string -> bool
  val is_theory_begin: string -> bool
  val is_theory: string -> bool
  val is_proof: string -> bool
  val is_theory_goal: string -> bool
  val is_proof_goal: string -> bool
  val is_schematic_goal: string -> bool
  val is_qed: string -> bool
  val is_qed_global: string -> bool
end;

structure Keyword: KEYWORD =
struct

(** keyword classification **)

datatype T = Keyword of string * string list;  (*kind, tags (in canonical reverse order)*)

fun kind s = Keyword (s, []);
fun kind_of (Keyword (s, _)) = s;


(* kinds *)

val control = kind "control";
val diag = kind "diag";
val thy_begin = kind "theory-begin";
val thy_switch = kind "theory-switch";
val thy_end = kind "theory-end";
val thy_heading = kind "theory-heading";
val thy_decl = kind "theory-decl";
val thy_script = kind "theory-script";
val thy_goal = kind "theory-goal";
val thy_schematic_goal = kind "theory-schematic-goal";
val qed = kind "qed";
val qed_block = kind "qed-block";
val qed_global = kind "qed-global";
val prf_heading = kind "proof-heading";
val prf_goal = kind "proof-goal";
val prf_block = kind "proof-block";
val prf_open = kind "proof-open";
val prf_close = kind "proof-close";
val prf_chain = kind "proof-chain";
val prf_decl = kind "proof-decl";
val prf_asm = kind "proof-asm";
val prf_asm_goal = kind "proof-asm-goal";
val prf_script = kind "proof-script";

val kinds =
  [control, diag, thy_begin, thy_switch, thy_end, thy_heading, thy_decl, thy_script, thy_goal,
    thy_schematic_goal, qed, qed_block, qed_global, prf_heading, prf_goal, prf_block, prf_open,
    prf_close, prf_chain, prf_decl, prf_asm, prf_asm_goal, prf_script]
 |> map kind_of;


(* tags *)

fun tag t (Keyword (s, ts)) = Keyword (s, update (op =) t ts);
fun tags_of (Keyword (_, ts)) = ts;

val tag_theory = tag "theory";
val tag_proof = tag "proof";
val tag_ml = tag "ML";


(* external names *)

val name_table = Symtab.make
  [("control",            control),
   ("diag",               diag),
   ("thy_begin",          thy_begin),
   ("thy_switch",         thy_switch),
   ("thy_end",            thy_end),
   ("thy_heading",        thy_heading),
   ("thy_decl",           thy_decl),
   ("thy_script",         thy_script),
   ("thy_goal",           thy_goal),
   ("thy_schematic_goal", thy_schematic_goal),
   ("qed",                qed),
   ("qed_block",          qed_block),
   ("qed_global",         qed_global),
   ("prf_heading",        prf_heading),
   ("prf_goal",           prf_goal),
   ("prf_block",          prf_block),
   ("prf_open",           prf_open),
   ("prf_close",          prf_close),
   ("prf_chain",          prf_chain),
   ("prf_decl",           prf_decl),
   ("prf_asm",            prf_asm),
   ("prf_asm_goal",       prf_asm_goal),
   ("prf_script",         prf_script)];

type spec = string * string list;

fun spec (kind, tags) =
  (case Symtab.lookup name_table kind of
    SOME k => k |> fold tag tags
  | NONE => error ("Unknown outer syntax keyword kind " ^ quote kind));

fun command_spec (name, s) = (name, spec s);



(** global keyword tables **)

type keywords =
 {lexicons: Scan.lexicon * Scan.lexicon,  (*minor, major*)
  commands: T Symtab.table};  (*command classification*)

fun make_keywords (lexicons, commands) : keywords =
  {lexicons = lexicons, commands = commands};

local

val global_keywords =
  Unsynchronized.ref (make_keywords ((Scan.empty_lexicon, Scan.empty_lexicon), Symtab.empty));

in

fun get_keywords () = ! global_keywords;

fun change_keywords f = CRITICAL (fn () =>
  Unsynchronized.change global_keywords
    (fn {lexicons, commands} => make_keywords (f (lexicons, commands))));

end;

fun get_lexicons () = #lexicons (get_keywords ());
fun get_commands () = #commands (get_keywords ());


(* lookup *)

fun is_keyword s =
  let
    val (minor, major) = get_lexicons ();
    val syms = Symbol.explode s;
  in Scan.is_literal minor syms orelse Scan.is_literal major syms end;

fun command_keyword name = Symtab.lookup (get_commands ()) name;
fun command_tags name = these (Option.map tags_of (command_keyword name));

fun dest () = pairself (sort_strings o Scan.dest_lexicon) (get_lexicons ());


(* status *)

val keyword_statusN = "keyword_status";

fun status_message m s =
  Position.setmp_thread_data Position.none
    (if print_mode_active keyword_statusN then Output.protocol_message m else writeln) s;

fun keyword_status name =
  status_message (Isabelle_Markup.keyword_decl name)
    ("Outer syntax keyword: " ^ quote name);

fun command_status (name, kind) =
  status_message (Isabelle_Markup.command_decl name (kind_of kind))
    ("Outer syntax command: " ^ quote name ^ " (" ^ kind_of kind ^ ")");

fun status () =
  let
    val {lexicons = (minor, _), commands} = get_keywords ();
    val _ = List.app keyword_status (sort_strings (Scan.dest_lexicon minor));
    val _ = List.app command_status (sort_wrt #1 (Symtab.dest commands));
  in () end;


(* define *)

fun define (name, NONE) =
     (change_keywords (fn ((minor, major), commands) =>
        let
          val minor' = Scan.extend_lexicon (Symbol.explode name) minor;
        in ((minor', major), commands) end);
      keyword_status name)
  | define (name, SOME kind) =
     (change_keywords (fn ((minor, major), commands) =>
        let
          val major' = Scan.extend_lexicon (Symbol.explode name) major;
          val commands' = Symtab.update (name, kind) commands;
        in ((minor, major'), commands') end);
      command_status (name, kind));


(* command categories *)

fun command_category ks name =
  (case command_keyword name of
    NONE => false
  | SOME k => member (op = o pairself kind_of) ks k);

val is_diag = command_category [diag];
val is_control = command_category [control];
val is_regular = not o command_category [diag, control];

val is_heading = command_category [thy_heading, prf_heading];

val is_theory_begin = command_category [thy_begin];

val is_theory = command_category
  [thy_begin, thy_switch, thy_end, thy_heading, thy_decl, thy_script, thy_goal, thy_schematic_goal];

val is_proof = command_category
  [qed, qed_block, qed_global, prf_heading, prf_goal, prf_block, prf_open, prf_close,
    prf_chain, prf_decl, prf_asm, prf_asm_goal, prf_script];

val is_theory_goal = command_category [thy_goal, thy_schematic_goal];
val is_proof_goal = command_category [prf_goal, prf_asm_goal];
val is_schematic_goal = command_category [thy_schematic_goal];
val is_qed = command_category [qed, qed_block];
val is_qed_global = command_category [qed_global];

end;

