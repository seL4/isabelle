(*  Title:      Pure/Isar/outer_keyword.ML
    ID:         $Id$
    Author:     Makarius

Isar command keyword classification.
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
end;

structure OuterKeyword: OUTER_KEYWORD =
struct

(* keyword classification *)

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

end;
