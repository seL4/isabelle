(*  Title:      Pure/Isar/isar_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Derived theory operations.

TODO:
  - pure_thy.ML: add_constdefs (atomic!);
  - 'methods' section (proof macros, ML method defs) (!?);
  - next_block: ProofHistory open / close (!?);
*)

signature ISAR_THY =
sig
  val add_text: string -> theory -> theory
  val add_title: string -> string -> string -> theory -> theory
  val add_chapter: string -> theory -> theory
  val add_section: string -> theory -> theory
  val add_subsection: string -> theory -> theory
  val add_subsubsection: string -> theory -> theory
  val add_axioms: ((bstring * string) * Args.src list) list -> theory -> theory
  val add_defs: ((bstring * string) * Args.src list) list -> theory -> theory
  val have_theorems: (bstring * Args.src list) * (xstring * Args.src list) list
    -> theory -> theory
  val have_lemmas: (bstring * Args.src list) * (xstring * Args.src list) list
    -> theory -> theory
  val have_facts: (string * Args.src list) * (string * Args.src list) list
    -> ProofHistory.T -> ProofHistory.T
  val fix: (string * string option) list -> ProofHistory.T -> ProofHistory.T
  val match_bind: (string list * string) list -> ProofHistory.T -> ProofHistory.T
  val theorem: string -> Args.src list -> string * string list -> theory -> ProofHistory.T
  val lemma: string -> Args.src list -> string * string list -> theory -> ProofHistory.T
  val assume: string -> Args.src list -> (string * string list) list
    -> ProofHistory.T -> ProofHistory.T
  val show: string -> Args.src list -> string * string list -> ProofHistory.T -> ProofHistory.T
  val have: string -> Args.src list -> string * string list -> ProofHistory.T -> ProofHistory.T
  val chain: ProofHistory.T -> ProofHistory.T
  val from_facts: (string * Args.src list) list -> ProofHistory.T -> ProofHistory.T
  val begin_block: ProofHistory.T -> ProofHistory.T
  val next_block: ProofHistory.T -> ProofHistory.T
  val end_block: ProofHistory.T -> ProofHistory.T
  val qed_with: bstring option * Args.src list option -> ProofHistory.T -> theory
  val qed: ProofHistory.T -> theory
  val kill_proof: ProofHistory.T -> theory
  val tac: Method.text -> ProofHistory.T -> ProofHistory.T
  val then_tac: Method.text -> ProofHistory.T -> ProofHistory.T
  val proof: Method.text option -> ProofHistory.T -> ProofHistory.T
  val terminal_proof: Method.text -> ProofHistory.T -> ProofHistory.T
  val immediate_proof: ProofHistory.T -> ProofHistory.T
  val default_proof: ProofHistory.T -> ProofHistory.T
  val use_mltext: string -> theory option -> theory option
  val use_mltext_theory: string -> theory -> theory
  val use_setup: string -> theory -> theory
  val parse_ast_translation: string -> theory -> theory
  val parse_translation: string -> theory -> theory
  val print_translation: string -> theory -> theory
  val typed_print_translation: string -> theory -> theory
  val print_ast_translation: string -> theory -> theory
  val token_translation: string -> theory -> theory
  val add_oracle: bstring * string -> theory -> theory
  val begin_theory: string -> string list -> (string * bool) list -> theory
  val end_theory: theory -> theory
  val theory: string * string list * (string * bool) list
    -> Toplevel.transition -> Toplevel.transition
  val context: string -> Toplevel.transition -> Toplevel.transition
  val update_context: string -> Toplevel.transition -> Toplevel.transition
end;

structure IsarThy: ISAR_THY =
struct


(** derived theory and proof operations **)

(* formal comments *)	(* FIXME dummy *)

fun add_text (txt:string) (thy:theory) = thy;
fun add_title title author date thy = thy;
val add_chapter = add_text;
val add_section = add_text;
val add_subsection = add_text;
val add_subsubsection = add_text;


(* axioms and defs *)

fun add_axms f args thy =
  f (map (fn (x, srcs) => (x, map (Attrib.global_attribute thy) srcs)) args) thy;

val add_axioms = add_axms PureThy.add_axioms;
val add_defs = add_axms PureThy.add_defs;


(* theorems *)

fun gen_have_thmss get attrib f ((name, more_srcs), th_srcs) x =
  f name (map (attrib x) more_srcs)
    (map (fn (s, srcs) => (get x s, map (attrib x) srcs)) th_srcs) x;


val have_theorems =
  #1 oo gen_have_thmss PureThy.get_thms Attrib.global_attribute PureThy.have_thmss;

val have_lemmas =
  #1 oo gen_have_thmss PureThy.get_thms Attrib.global_attribute
    (fn name => fn more_atts => PureThy.have_thmss name (more_atts @ [Drule.tag_lemma]));


val have_thmss =
  gen_have_thmss (ProofContext.get_thms o Proof.context_of)
    (Attrib.local_attribute o Proof.theory_of) Proof.have_thmss;

val have_facts = ProofHistory.apply o have_thmss;
val from_facts = ProofHistory.apply o (Proof.chain oo curry have_thmss ("", []));


(* context *)

val fix = ProofHistory.apply o Proof.fix;

val match_bind = ProofHistory.apply o Proof.match_bind;


(* statements *)

fun global_statement f name tags s thy =
  ProofHistory.init (f name (map (Attrib.global_attribute thy) tags) s thy);

fun local_statement f name tags s = ProofHistory.apply_open (fn state =>
  f name (map (Attrib.local_attribute (Proof.theory_of state)) tags) s state);

val theorem = global_statement Proof.theorem;
val lemma = global_statement Proof.lemma;
val assume = local_statement Proof.assume;
val show = local_statement Proof.show;
val have = local_statement Proof.have;


(* forward chaining *)

val chain = ProofHistory.apply Proof.chain;


(* end proof *)

fun qed_with (alt_name, alt_tags) prf =
  let
    val state = ProofHistory.current prf;
    val thy = Proof.theory_of state;
    val alt_atts = apsome (map (Attrib.global_attribute thy)) alt_tags;
    val (thy', (kind, name, thm)) = Method.qed alt_name alt_atts state;

    val prt_result = Pretty.block
      [Pretty.str (kind ^ " " ^ name ^ ":"), Pretty.fbrk, Display.pretty_thm thm];
  in Pretty.writeln prt_result; thy end;

val qed = qed_with (None, None);

val kill_proof = Proof.theory_of o ProofHistory.current;


(* blocks *)

val begin_block = ProofHistory.apply_open Proof.begin_block;
val next_block = ProofHistory.apply Proof.next_block;


(* backward steps *)

val tac = ProofHistory.applys o Method.tac;
val then_tac = ProofHistory.applys o Method.then_tac;
val proof = ProofHistory.applys o Method.proof;
val end_block = ProofHistory.applys_close Method.end_block;
val terminal_proof = ProofHistory.applys_close o Method.terminal_proof;
val immediate_proof = ProofHistory.applys_close Method.immediate_proof;
val default_proof = ProofHistory.applys_close Method.default_proof;


(* use ML text *)

fun use_mltext txt opt_thy = #2 (Context.pass opt_thy (use_text false) txt);
fun use_mltext_theory txt thy = #2 (Context.pass_theory thy (use_text false) txt);

fun use_context txt = use_mltext_theory ("Context.>> (" ^ txt ^ ");");

fun use_let name body txt =
  use_context ("let val " ^ name ^ " = " ^ txt ^ " in\n" ^ body ^ " end");

val use_setup =
  use_let "setup: (theory -> theory) list" "Library.apply setup";


(* translation functions *)

val parse_ast_translation =
  use_let "parse_ast_translation: (string * (Syntax.ast list -> Syntax.ast)) list"
    "Theory.add_trfuns (parse_ast_translation, [], [], [])";

val parse_translation =
  use_let "parse_translation: (string * (term list -> term)) list"
    "Theory.add_trfuns ([], parse_translation, [], [])";

val print_translation =
  use_let "print_translation: (string * (term list -> term)) list"
    "Theory.add_trfuns ([], [], print_translation, [])";

val print_ast_translation =
  use_let "print_ast_translation: (string * (Syntax.ast list -> Syntax.ast)) list"
    "Theory.add_trfuns ([], [], [], print_ast_translation)";

val typed_print_translation =
  use_let "typed_print_translation: (string * (bool -> typ -> term list -> term)) list"
    "Theory.add_trfunsT typed_print_translation";

val token_translation =
  use_let "token_translation: (string * string * (string -> string * int)) list"
    "Theory.add_tokentrfuns token_translation";


(* add_oracle *)

fun add_oracle (name, txt) =
  use_let
    "oracle: bstring * (Sign.sg * Object.T -> term)"
    "Theory.add_oracle oracle"
    ("(" ^ quote name ^ ", " ^ txt ^ ")");


(* theory init and exit *)	(* FIXME move? rearrange? *)

fun begin_theory name parents files =
  let
    val paths = map (apfst Path.unpack) files;
    val thy = ThyInfo.begin_theory name parents paths;
  in Present.begin_theory name parents paths; thy end;


(* FIXME
fun end_theory thy =
  let val thy' = PureThy.end_theory thy in
    Present.end_theory (PureThy.get_name thy');
    transform_error ThyInfo.put_theory thy'
      handle exn => raise PureThy.ROLLBACK (thy', Some exn)     (* FIXME !!?? *)
  end;
*)

fun end_theory thy =
  (Present.end_theory (PureThy.get_name thy); ThyInfo.end_theory thy);

fun bg_theory (name, parents, files) () = begin_theory name parents files;
fun en_theory thy = (end_theory thy; ());

fun theory spec = Toplevel.init_theory (bg_theory spec) en_theory;


(* context switch *)

fun switch_theory load name =
  Toplevel.init_theory
    (fn () => (Context.save load name; ThyInfo.get_theory name)) (K ());

val context = switch_theory ThyInfo.use_thy;
val update_context = switch_theory ThyInfo.update_thy;


end;
