(*  Title:      Pure/Isar/outer_keyword.ML
    Author:     Makarius

Isar command keyword classification and global keyword tables.
*)

signature OUTER_KEYWORD =
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
  val update_tags: string -> string list -> string list
  val tag: string -> T -> T
  val tags_of: T -> string list
  val tag_theory: T -> T
  val tag_proof: T -> T
  val tag_ml: T -> T
  val get_lexicons: unit -> Scan.lexicon * Scan.lexicon
  val is_keyword: string -> bool
  val dest_keywords: unit -> string list
  val dest_commands: unit -> string list
  val command_keyword: string -> T option
  val command_tags: string -> string list
  val report: unit -> unit
  val keyword: string -> unit
  val command: string -> T -> unit
  val is_diag: string -> bool
  val is_control: string -> bool
  val is_regular: string -> bool
  val is_theory_begin: string -> bool
  val is_theory: string -> bool
  val is_proof: string -> bool
  val is_theory_goal: string -> bool
  val is_proof_goal: string -> bool
  val is_qed: string -> bool
  val is_qed_global: string -> bool
end;

structure OuterKeyword: OUTER_KEYWORD =
struct

(** keyword classification **)

datatype T = Keyword of string * string list;

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

val kinds = [control, diag, thy_begin, thy_switch, thy_end, thy_heading, thy_decl, thy_script,
  thy_goal, qed, qed_block, qed_global, prf_heading, prf_goal, prf_block, prf_open, prf_close,
  prf_chain, prf_decl, prf_asm, prf_asm_goal, prf_script] |> map kind_of;


(* tags *)

fun update_tags t ts = t :: remove (op = : string * string -> bool) t ts;

fun tag t (Keyword (s, ts)) = Keyword (s, update_tags t ts);
fun tags_of (Keyword (_, ts)) = ts;

val tag_theory = tag "theory";
val tag_proof = tag "proof";
val tag_ml = tag "ML";



(** global keyword tables **)

local

val global_commands = Unsynchronized.ref (Symtab.empty: T Symtab.table);
val global_lexicons = Unsynchronized.ref (Scan.empty_lexicon, Scan.empty_lexicon);

in

fun get_commands () = CRITICAL (fn () => ! global_commands);
fun get_lexicons () = CRITICAL (fn () => ! global_lexicons);

fun change_commands f = CRITICAL (fn () => Unsynchronized.change global_commands f);
fun change_lexicons f = CRITICAL (fn () => Unsynchronized.change global_lexicons f);

end;


(* lookup *)

fun is_keyword s = Scan.is_literal (#1 (get_lexicons ())) (Symbol.explode s);
fun dest_keywords () = sort_strings (Scan.dest_lexicon (#1 (get_lexicons ())));

fun dest_commands () = sort_strings (Symtab.keys (get_commands ()));
fun command_keyword name = Symtab.lookup (get_commands ()) name;
fun command_tags name = these (Option.map tags_of (command_keyword name));


(* report *)

fun report_keyword name =
  Pretty.mark (Markup.keyword_decl name)
    (Pretty.str ("Outer syntax keyword: " ^ quote name));

fun report_command (name, kind) =
  Pretty.mark (Markup.command_decl name (kind_of kind))
    (Pretty.str ("Outer syntax command: " ^ quote name ^ " (" ^ kind_of kind ^ ")"));

fun status_writeln s = (Output.status s; writeln s);

fun report () =
  let val (keywords, commands) = CRITICAL (fn () =>
    (dest_keywords (), sort_wrt #1 (Symtab.dest (get_commands ()))))
  in map report_keyword keywords @ map report_command commands end
  |> Pretty.chunks |> Pretty.string_of |> status_writeln;


(* augment tables *)

fun keyword name =
 (change_lexicons (apfst (Scan.extend_lexicon (Symbol.explode name)));
  status_writeln (Pretty.string_of (report_keyword name)));

fun command name kind =
 (change_lexicons (apsnd (Scan.extend_lexicon (Symbol.explode name)));
  change_commands (Symtab.update (name, kind));
  status_writeln (Pretty.string_of (report_command (name, kind))));


(* command categories *)

fun command_category ks name =
  (case command_keyword name of
    NONE => false
  | SOME k => member (op = o pairself kind_of) ks k);

val is_diag = command_category [diag];
val is_control = command_category [control];
fun is_regular name = not (is_diag name orelse is_control name);

val is_theory_begin = command_category [thy_begin];

val is_theory = command_category
  [thy_begin, thy_switch, thy_end, thy_heading, thy_decl, thy_script, thy_goal];

val is_proof = command_category
  [qed, qed_block, qed_global, prf_heading, prf_goal, prf_block, prf_open, prf_close,
    prf_chain, prf_decl, prf_asm, prf_asm_goal, prf_script];

val is_theory_goal = command_category [thy_goal];
val is_proof_goal = command_category [prf_goal, prf_asm_goal];
val is_qed = command_category [qed, qed_block];
val is_qed_global = command_category [qed_global];

end;
