(*  Title:      Pure/Isar/keyword.ML
    Author:     Makarius

Isar keyword classification.
*)

signature KEYWORD =
sig
  type T
  val kind_of: T -> string
  val kind_files_of: T -> string * string list
  val diag: T
  val heading: T
  val thy_begin: T
  val thy_end: T
  val thy_decl: T
  val thy_decl_block: T
  val thy_load: T
  val thy_goal: T
  val qed: T
  val qed_script: T
  val qed_block: T
  val qed_global: T
  val prf_goal: T
  val prf_block: T
  val prf_open: T
  val prf_close: T
  val prf_chain: T
  val prf_decl: T
  val prf_asm: T
  val prf_asm_goal: T
  val prf_asm_goal_script: T
  val prf_script: T
  type spec = (string * string list) * string list
  val spec: spec -> T
  val command_spec: (string * spec) * Position.T -> (string * T) * Position.T
  type keywords
  val minor_keywords: keywords -> Scan.lexicon
  val major_keywords: keywords -> Scan.lexicon
  val no_command_keywords: keywords -> keywords
  val empty_keywords: keywords
  val merge_keywords: keywords * keywords -> keywords
  val add_keywords: string * T option -> keywords -> keywords
  val is_keyword: keywords -> string -> bool
  val command_keyword: keywords -> string -> T option
  val command_files: keywords -> string -> Path.T -> Path.T list
  val command_tags: keywords -> string -> string list
  val is_diag: keywords -> string -> bool
  val is_heading: keywords -> string -> bool
  val is_theory_begin: keywords -> string -> bool
  val is_theory_load: keywords -> string -> bool
  val is_theory: keywords -> string -> bool
  val is_theory_body: keywords -> string -> bool
  val is_proof: keywords -> string -> bool
  val is_proof_body: keywords -> string -> bool
  val is_theory_goal: keywords -> string -> bool
  val is_proof_goal: keywords -> string -> bool
  val is_qed: keywords -> string -> bool
  val is_qed_global: keywords -> string -> bool
  val is_printed: keywords -> string -> bool
  val define: string * T option -> unit
  val get_keywords: unit -> keywords
end;

structure Keyword: KEYWORD =
struct

(** keyword classification **)

(* kinds *)

datatype T = Keyword of
 {kind: string,
  files: string list,  (*extensions of embedded files*)
  tags: string list};

fun kind s = Keyword {kind = s, files = [], tags = []};
fun kind_of (Keyword {kind, ...}) = kind;
fun kind_files_of (Keyword {kind, files, ...}) = (kind, files);

val diag = kind "diag";
val heading = kind "heading";
val thy_begin = kind "thy_begin";
val thy_end = kind "thy_end";
val thy_decl = kind "thy_decl";
val thy_decl_block = kind "thy_decl_block";
val thy_load = kind "thy_load";
val thy_goal = kind "thy_goal";
val qed = kind "qed";
val qed_script = kind "qed_script";
val qed_block = kind "qed_block";
val qed_global = kind "qed_global";
val prf_goal = kind "prf_goal";
val prf_block = kind "prf_block";
val prf_open = kind "prf_open";
val prf_close = kind "prf_close";
val prf_chain = kind "prf_chain";
val prf_decl = kind "prf_decl";
val prf_asm = kind "prf_asm";
val prf_asm_goal = kind "prf_asm_goal";
val prf_asm_goal_script = kind "prf_asm_goal_script";
val prf_script = kind "prf_script";

val kinds =
  [diag, heading, thy_begin, thy_end, thy_load, thy_decl, thy_decl_block, thy_goal,
    qed, qed_script, qed_block, qed_global, prf_goal, prf_block, prf_open, prf_close,
    prf_chain, prf_decl, prf_asm, prf_asm_goal, prf_asm_goal_script, prf_script]
  |> map kind_of;


(* specifications *)

type spec = (string * string list) * string list;

fun spec ((kind, files), tags) =
  if not (member (op =) kinds kind) then
    error ("Unknown outer syntax keyword kind " ^ quote kind)
  else if not (null files) andalso kind <> kind_of thy_load then
    error ("Illegal specification of files for " ^ quote kind)
  else Keyword {kind = kind, files = files, tags = tags};

fun command_spec ((name, s), pos) = ((name, spec s), pos);



(** keyword tables **)

(* type keywords *)

datatype keywords = Keywords of
 {minor: Scan.lexicon,
  major: Scan.lexicon,
  commands: T Symtab.table};

fun minor_keywords (Keywords {minor, ...}) = minor;
fun major_keywords (Keywords {major, ...}) = major;

fun make_keywords (minor, major, commands) =
  Keywords {minor = minor, major = major, commands = commands};

fun map_keywords f (Keywords {minor, major, commands}) =
  make_keywords (f (minor, major, commands));

val no_command_keywords =
  map_keywords (fn (minor, _, _) => (minor, Scan.empty_lexicon, Symtab.empty));


(* build keywords *)

val empty_keywords =
  make_keywords (Scan.empty_lexicon, Scan.empty_lexicon, Symtab.empty);

fun merge_keywords
  (Keywords {minor = minor1, major = major1, commands = commands1},
    Keywords {minor = minor2, major = major2, commands = commands2}) =
  make_keywords
   (Scan.merge_lexicons (minor1, minor2),
    Scan.merge_lexicons (major1, major2),
    Symtab.merge (K true) (commands1, commands2));

fun add_keywords (name, opt_kind) = map_keywords (fn (minor, major, commands) =>
  (case opt_kind of
    NONE =>
      let
        val minor' = Scan.extend_lexicon (Symbol.explode name) minor;
      in (minor', major, commands) end
  | SOME kind =>
      let
        val major' = Scan.extend_lexicon (Symbol.explode name) major;
        val commands' = Symtab.update (name, kind) commands;
      in (minor, major', commands') end));


(* lookup *)

fun is_keyword keywords s =
  let
    val minor = minor_keywords keywords;
    val major = major_keywords keywords;
    val syms = Symbol.explode s;
  in Scan.is_literal minor syms orelse Scan.is_literal major syms end;

fun command_keyword (Keywords {commands, ...}) = Symtab.lookup commands;

fun command_files keywords name path =
  (case command_keyword keywords name of
    NONE => []
  | SOME (Keyword {kind, files, ...}) =>
      if kind <> kind_of thy_load then []
      else if null files then [path]
      else map (fn ext => Path.ext ext path) files);

fun command_tags keywords name =
  (case command_keyword keywords name of
    SOME (Keyword {tags, ...}) => tags
  | NONE => []);


(* command categories *)

fun command_category ks =
  let
    val tab = Symtab.make_set (map kind_of ks);
    fun pred keywords name =
      (case command_keyword keywords name of
        NONE => false
      | SOME k => Symtab.defined tab (kind_of k));
  in pred end;

val is_diag = command_category [diag];

val is_heading = command_category [heading];

val is_theory_begin = command_category [thy_begin];

val is_theory_load = command_category [thy_load];

val is_theory = command_category
  [thy_begin, thy_end, thy_load, thy_decl, thy_decl_block, thy_goal];

val is_theory_body = command_category
  [thy_load, thy_decl, thy_decl_block, thy_goal];

val is_proof = command_category
  [qed, qed_script, qed_block, qed_global, prf_goal, prf_block, prf_open, prf_close,
    prf_chain, prf_decl, prf_asm, prf_asm_goal, prf_asm_goal_script, prf_script];

val is_proof_body = command_category
  [diag, heading, prf_block, prf_open, prf_close, prf_chain, prf_decl, prf_asm,
    prf_asm_goal, prf_asm_goal_script, prf_script];

val is_theory_goal = command_category [thy_goal];
val is_proof_goal = command_category [prf_goal, prf_asm_goal, prf_asm_goal_script];
val is_qed = command_category [qed, qed_script, qed_block];
val is_qed_global = command_category [qed_global];

fun is_printed keywords = is_theory_goal keywords orf is_proof keywords;



(** global state **)

local val global_keywords = Unsynchronized.ref empty_keywords in

fun define decl = CRITICAL (fn () => Unsynchronized.change global_keywords (add_keywords decl));
fun get_keywords () = ! global_keywords;

end;

end;

