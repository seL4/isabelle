(*  Title:      Pure/Isar/isar_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Pure/Isar derived theory operations.

TODO:
  - 'methods' section (proof macros, ML method defs) (!?);
  - next_block: ProofHistory open / close (!?);
*)

signature ISAR_THY =
sig
  val add_text: Comment.text -> theory -> theory
  val add_title: Comment.text -> Comment.text -> Comment.text -> theory -> theory
  val add_chapter: Comment.text -> theory -> theory
  val add_section: Comment.text -> theory -> theory
  val add_subsection: Comment.text -> theory -> theory
  val add_subsubsection: Comment.text -> theory -> theory
  val add_axioms: ((bstring * string) * Args.src list) list -> theory -> theory
  val add_axioms_i: ((bstring * term) * theory attribute list) list -> theory -> theory
  val add_defs: ((bstring * string) * Args.src list) list -> theory -> theory
  val add_defs_i: ((bstring * term) * theory attribute list) list -> theory -> theory
  val add_constdefs: ((bstring * string * mixfix) * string) list -> theory -> theory
  val add_constdefs_i: ((bstring * typ * mixfix) * term) list -> theory -> theory
  val apply_theorems: (xstring * Args.src list) list -> theory -> theory * thm list
  val apply_theorems_i: (thm * theory attribute list) list -> theory -> theory * thm list
  val have_theorems: (bstring * Args.src list) * (xstring * Args.src list) list
    -> theory -> theory
  val have_theorems_i: (bstring * theory attribute list) * (thm * theory attribute list) list
    -> theory -> theory
  val have_lemmas: (bstring * Args.src list) * (xstring * Args.src list) list
    -> theory -> theory
  val have_lemmas_i: (bstring * theory attribute list) * (thm * theory attribute list) list
    -> theory -> theory
  val have_facts: (string * Args.src list) * (string * Args.src list) list
    -> ProofHistory.T -> ProofHistory.T
  val have_facts_i: (string * Proof.context attribute list) *
    (thm * Proof.context attribute list) list -> ProofHistory.T -> ProofHistory.T
  val from_facts: (string * Args.src list) list -> ProofHistory.T -> ProofHistory.T
  val from_facts_i: (thm * Proof.context attribute list) list -> ProofHistory.T -> ProofHistory.T
  val chain: ProofHistory.T -> ProofHistory.T
  val fix: (string * string option) list -> ProofHistory.T -> ProofHistory.T
  val fix_i: (string * typ) list -> ProofHistory.T -> ProofHistory.T
  val match_bind: (string list * string) list -> ProofHistory.T -> ProofHistory.T
  val match_bind_i: (term list * term) list -> ProofHistory.T -> ProofHistory.T
  val theorem: string -> Args.src list -> string * string list -> theory -> ProofHistory.T
  val theorem_i: bstring -> theory attribute list -> term * term list -> theory -> ProofHistory.T
  val lemma: string -> Args.src list -> string * string list -> theory -> ProofHistory.T
  val lemma_i: bstring -> theory attribute list -> term * term list -> theory -> ProofHistory.T
  val assume: string -> Args.src list -> (string * string list) list
    -> ProofHistory.T -> ProofHistory.T
  val assume_i: string -> Proof.context attribute list -> (term * term list) list
    -> ProofHistory.T -> ProofHistory.T
  val show: string -> Args.src list -> string * string list -> ProofHistory.T -> ProofHistory.T
  val show_i: string -> Proof.context attribute list -> term * term list
    -> ProofHistory.T -> ProofHistory.T
  val have: string -> Args.src list -> string * string list -> ProofHistory.T -> ProofHistory.T
  val have_i: string -> Proof.context attribute list -> term * term list
    -> ProofHistory.T -> ProofHistory.T
  val thus: string -> Args.src list -> string * string list -> ProofHistory.T -> ProofHistory.T
  val thus_i: string -> Proof.context attribute list -> term * term list
    -> ProofHistory.T -> ProofHistory.T
  val hence: string -> Args.src list -> string * string list -> ProofHistory.T -> ProofHistory.T
  val hence_i: string -> Proof.context attribute list -> term * term list
    -> ProofHistory.T -> ProofHistory.T
  val begin_block: ProofHistory.T -> ProofHistory.T
  val next_block: ProofHistory.T -> ProofHistory.T
  val end_block: ProofHistory.T -> ProofHistory.T
  val tac: Method.text -> ProofHistory.T -> ProofHistory.T
  val then_tac: Method.text -> ProofHistory.T -> ProofHistory.T
  val proof: Method.text option -> ProofHistory.T -> ProofHistory.T
  val kill_proof: ProofHistory.T -> theory
  val global_qed_with: bstring option * Args.src list option -> Method.text option
    -> Toplevel.transition -> Toplevel.transition
  val global_qed_with_i: bstring option * theory attribute list option -> Method.text option
    -> Toplevel.transition -> Toplevel.transition
  val qed: Method.text option -> Toplevel.transition -> Toplevel.transition
  val terminal_proof: Method.text -> Toplevel.transition -> Toplevel.transition
  val immediate_proof: Toplevel.transition -> Toplevel.transition
  val default_proof: Toplevel.transition -> Toplevel.transition
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

(* formal comments *)   (* FIXME dummy *)

fun add_text _ thy = thy;
fun add_title title author date thy = thy;
val add_chapter = add_text;
val add_section = add_text;
val add_subsection = add_text;
val add_subsubsection = add_text;


(* axioms and defs *)

fun add_axms f args thy =
  f (map (fn (x, srcs) => (x, map (Attrib.global_attribute thy) srcs)) args) thy;

val add_axioms = add_axms PureThy.add_axioms;
val add_axioms_i = PureThy.add_axioms_i;
val add_defs = add_axms PureThy.add_defs;
val add_defs_i = PureThy.add_defs_i;


(* constdefs *)

fun gen_add_constdefs consts defs args thy =
  thy
  |> consts (map fst args)
  |> defs (map (fn ((c, _, mx), s) => ((Thm.def_name (Syntax.const_name c mx), s), [])) args);

val add_constdefs = gen_add_constdefs Theory.add_consts add_defs;
val add_constdefs_i = gen_add_constdefs Theory.add_consts_i add_defs_i;


(* theorems *)

fun gen_have_thmss get attrib f ((name, more_srcs), th_srcs) x =
  f name (map (attrib x) more_srcs)
    (map (fn (s, srcs) => (get x s, map (attrib x) srcs)) th_srcs) x;

fun global_have_thmss x = gen_have_thmss PureThy.get_thms Attrib.global_attribute x;

fun local_have_thmss x =
  gen_have_thmss (ProofContext.get_thms o Proof.context_of)
    (Attrib.local_attribute o Proof.theory_of) x;

fun have_thmss_i f ((name, more_atts), th_atts) =
  f name more_atts (map (apfst single) th_atts);

fun have_lemss name atts = PureThy.have_thmss name (atts @ [Drule.tag_lemma]);


fun apply_theorems th_srcs = global_have_thmss PureThy.have_thmss ((None, []), th_srcs);
fun apply_theorems_i th_srcs = have_thmss_i PureThy.have_thmss ((None, []), th_srcs);
val have_theorems = #1 oo global_have_thmss (PureThy.have_thmss o Some);
val have_theorems_i = #1 oo have_thmss_i (PureThy.have_thmss o Some);
val have_lemmas = #1 oo global_have_thmss (have_lemss o Some);
val have_lemmas_i = #1 oo have_thmss_i (have_lemss o Some);
val have_facts = ProofHistory.apply o local_have_thmss Proof.have_thmss;
val have_facts_i = ProofHistory.apply o have_thmss_i Proof.have_thmss;


(* forward chaining *)

val from_facts =
  ProofHistory.apply o (Proof.chain oo curry (local_have_thmss Proof.have_thmss) ("", []));

val from_facts_i =
  ProofHistory.apply o (Proof.chain oo curry (have_thmss_i Proof.have_thmss) ("", []));

val chain = ProofHistory.apply Proof.chain;


(* context *)

val fix = ProofHistory.apply o Proof.fix;
val fix_i = ProofHistory.apply o Proof.fix_i;
val match_bind = ProofHistory.apply o Proof.match_bind;
val match_bind_i = ProofHistory.apply o Proof.match_bind_i;


(* statements *)

fun global_statement f name src s thy =
  ProofHistory.init (f name (map (Attrib.global_attribute thy) src) s thy);

fun global_statement_i f name atts t thy = ProofHistory.init (f name atts t thy);

fun local_statement do_open f g name src s = ProofHistory.apply_cond_open do_open (fn state =>
  f name (map (Attrib.local_attribute (Proof.theory_of state)) src) s (g state));

fun local_statement_i do_open f g name atts t =
  ProofHistory.apply_cond_open do_open (f name atts t o g);

val theorem   = global_statement Proof.theorem;
val theorem_i = global_statement_i Proof.theorem_i;
val lemma     = global_statement Proof.lemma;
val lemma_i   = global_statement_i Proof.lemma_i;
val assume    = local_statement false Proof.assume I;
val assume_i  = local_statement_i false Proof.assume_i I;
val show      = local_statement true Proof.show I;
val show_i    = local_statement_i true Proof.show_i I;
val have      = local_statement true Proof.have I;
val have_i    = local_statement_i true Proof.have_i I;
val thus      = local_statement true Proof.show Proof.chain;
val thus_i    = local_statement_i true Proof.show_i Proof.chain;
val hence     = local_statement true Proof.have Proof.chain;
val hence_i   = local_statement_i true Proof.have_i Proof.chain;


(* blocks *)

val begin_block = ProofHistory.apply_open Proof.begin_block;
val next_block = ProofHistory.apply Proof.next_block;
val end_block = ProofHistory.apply_close Proof.end_block;


(* backward steps *)

val tac = ProofHistory.applys o Method.tac;
val then_tac = ProofHistory.applys o Method.then_tac;
val proof = ProofHistory.applys o Method.proof;


(* local endings *)

(* FIXME
val print_proof = Toplevel.print oo Toplevel.proof;
*)
val print_proof = Toplevel.proof;

val local_qed = print_proof o ProofHistory.applys_close o Method.local_qed;
val local_terminal_proof = print_proof o ProofHistory.applys_close o Method.local_terminal_proof;
val local_immediate_proof = print_proof (ProofHistory.applys_close Method.local_immediate_proof);
val local_default_proof = print_proof (ProofHistory.applys_close Method.local_default_proof);


(* global endings *)

val kill_proof = Proof.theory_of o ProofHistory.current;

fun global_result finish = Toplevel.proof_to_theory (fn prf =>
  let
    val state = ProofHistory.current prf;
    val _ = if Proof.at_bottom state then () else raise Toplevel.UNDEF;
    val (thy, {kind, name, thm}) = finish state;

    val prt_result = Pretty.block
      [Pretty.str (kind ^ " " ^ name ^ ":"), Pretty.fbrk, Display.pretty_thm thm];
  in Pretty.writeln prt_result; thy end);

fun gen_global_qed_with prep_att (alt_name, raw_atts) opt_text state =
  let
    val thy = Proof.theory_of state;
    val alt_atts = apsome (map (prep_att thy)) raw_atts;
  in Method.global_qed alt_name alt_atts opt_text state end;

val global_qed_with = global_result oo gen_global_qed_with Attrib.global_attribute;
val global_qed_with_i = global_result oo gen_global_qed_with (K I);
val global_qed = global_qed_with (None, None);

val global_terminal_proof = global_result o Method.global_terminal_proof;
val global_immediate_proof = global_result Method.global_immediate_proof;
val global_default_proof = global_result Method.global_default_proof;


(* common endings *)

fun qed opt_text = local_qed opt_text o global_qed opt_text;
fun terminal_proof opt_text = local_terminal_proof opt_text o global_terminal_proof opt_text;
val immediate_proof = local_immediate_proof o global_immediate_proof;
val default_proof = local_default_proof o global_default_proof;


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


(* theory init and exit *)      (* FIXME move? rearrange? *)

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

fun switch_theory load s =
  Toplevel.init_theory (fn () => (the (#2 (Context.pass None load s)))) (K ());

val context = switch_theory ThyInfo.use_thy;
val update_context = switch_theory ThyInfo.update_thy;


end;
