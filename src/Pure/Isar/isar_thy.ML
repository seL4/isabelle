(*  Title:      Pure/Isar/isar_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Pure/Isar derived theory operations.
*)

signature ISAR_THY =
sig
  val add_text: Comment.text -> theory -> theory
  val add_title: Comment.text -> Comment.text -> Comment.text -> theory -> theory
  val add_chapter: Comment.text -> theory -> theory
  val add_section: Comment.text -> theory -> theory
  val add_subsection: Comment.text -> theory -> theory
  val add_subsubsection: Comment.text -> theory -> theory
  val add_classes: (bclass * xclass list) list * Comment.text -> theory -> theory
  val add_classes_i: (bclass * class list) list * Comment.text  -> theory -> theory
  val add_classrel: (xclass * xclass) * Comment.text -> theory -> theory
  val add_classrel_i: (class * class) * Comment.text -> theory -> theory
  val add_defsort: xsort * Comment.text -> theory -> theory
  val add_defsort_i: sort * Comment.text -> theory -> theory
  val add_nonterminals: (bstring * Comment.text) list -> theory -> theory
  val add_tyabbrs: ((bstring * string list * string * mixfix) * Comment.text) list
    -> theory -> theory
  val add_tyabbrs_i: ((bstring * string list * typ * mixfix) * Comment.text) list
    -> theory -> theory
  val add_arities: ((xstring * xsort list * xsort) * Comment.text) list -> theory -> theory
  val add_arities_i: ((string * sort list * sort) * Comment.text) list -> theory -> theory
  val add_typedecl: (bstring * string list * mixfix) * Comment.text -> theory -> theory
  val add_consts: ((bstring * string * mixfix) * Comment.text) list -> theory -> theory
  val add_consts_i: ((bstring * typ * mixfix) * Comment.text) list -> theory -> theory
  val add_modesyntax: string * bool -> ((bstring * string * mixfix) * Comment.text) list
    -> theory -> theory
  val add_modesyntax_i: string * bool -> ((bstring * typ * mixfix) * Comment.text) list
    -> theory -> theory
  val add_trrules: ((xstring * string) Syntax.trrule * Comment.text) list -> theory -> theory
  val add_trrules_i: (Syntax.ast Syntax.trrule * Comment.text) list -> theory -> theory
  val add_axioms: (((bstring * string) * Args.src list) * Comment.text) list -> theory -> theory
  val add_axioms_i: (((bstring * term) * theory attribute list) * Comment.text) list
    -> theory -> theory
  val add_defs: (((bstring * string) * Args.src list) * Comment.text) list -> theory -> theory
  val add_defs_i: (((bstring * term) * theory attribute list) * Comment.text) list
    -> theory -> theory
  val add_constdefs: (((bstring * string * mixfix) * Comment.text) * (string * Comment.text)) list
    -> theory -> theory
  val add_constdefs_i: (((bstring * typ * mixfix) * Comment.text) * (term * Comment.text)) list
    -> theory -> theory
  val apply_theorems: (xstring * Args.src list) list -> theory -> theory * thm list
  val apply_theorems_i: (thm * theory attribute list) list -> theory -> theory * thm list
  val have_theorems: ((bstring * Args.src list) * (xstring * Args.src list) list) * Comment.text
    -> theory -> theory
  val have_theorems_i: ((bstring * theory attribute list) * (thm * theory attribute list) list)
    * Comment.text -> theory -> theory
  val have_lemmas: ((bstring * Args.src list) * (xstring * Args.src list) list) * Comment.text
    -> theory -> theory
  val have_lemmas_i: ((bstring * theory attribute list) * (thm * theory attribute list) list)
    * Comment.text -> theory -> theory
  val have_facts: ((string * Args.src list) * (string * Args.src list) list) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val have_facts_i: ((string * Proof.context attribute list) *
    (thm * Proof.context attribute list) list) * Comment.text -> ProofHistory.T -> ProofHistory.T
  val from_facts: (string * Args.src list) list * Comment.text -> ProofHistory.T -> ProofHistory.T
  val from_facts_i: (thm * Proof.context attribute list) list * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val chain: Comment.text -> ProofHistory.T -> ProofHistory.T
  val fix: (string * string option) list * Comment.text -> ProofHistory.T -> ProofHistory.T
  val fix_i: (string * typ) list * Comment.text -> ProofHistory.T -> ProofHistory.T
  val match_bind: ((string list * string) * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val match_bind_i: ((term list * term) * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val theorem: (bstring * Args.src list * (string * string list)) * Comment.text
    -> bool -> theory -> ProofHistory.T
  val theorem_i: (bstring * theory attribute list * (term * term list)) * Comment.text
    -> bool -> theory -> ProofHistory.T
  val lemma: (bstring * Args.src list * (string * string list)) * Comment.text
    -> bool -> theory -> ProofHistory.T
  val lemma_i: (bstring * theory attribute list * (term * term list)) * Comment.text
    -> bool -> theory -> ProofHistory.T
  val assume: (string * Args.src list * (string * string list) list) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val assume_i: (string * Proof.context attribute list * (term * term list) list) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val show: (string * Args.src list * (string * string list)) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val show_i: (string * Proof.context attribute list * (term * term list)) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val have: (string * Args.src list * (string * string list)) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val have_i: (string * Proof.context attribute list * (term * term list)) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val thus: (string * Args.src list * (string * string list)) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val thus_i: (string * Proof.context attribute list * (term * term list)) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val hence: (string * Args.src list * (string * string list)) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val hence_i: (string * Proof.context attribute list * (term * term list)) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val begin_block: ProofHistory.T -> ProofHistory.T
  val next_block: ProofHistory.T -> ProofHistory.T
  val end_block: ProofHistory.T -> ProofHistory.T
  val tac: Method.text -> ProofHistory.T -> ProofHistory.T
  val then_tac: Method.text -> ProofHistory.T -> ProofHistory.T
  val proof: Comment.interest * (Method.text * Comment.interest) option
    -> ProofHistory.T -> ProofHistory.T
  val kill_proof: ProofHistory.T -> theory
  val global_qed_with: bstring option * Args.src list option
    -> (Method.text * Comment.interest) option
    -> Toplevel.transition -> Toplevel.transition
  val global_qed_with_i: bstring option * theory attribute list option
    -> (Method.text * Comment.interest) option
    -> Toplevel.transition -> Toplevel.transition
  val qed: (Method.text * Comment.interest) option -> Toplevel.transition -> Toplevel.transition
  val terminal_proof: Method.text * Comment.interest -> Toplevel.transition -> Toplevel.transition
  val immediate_proof: Toplevel.transition -> Toplevel.transition
  val default_proof: Toplevel.transition -> Toplevel.transition
  val also: Comment.text -> Toplevel.transition -> Toplevel.transition
  val finally: Comment.text -> Toplevel.transition -> Toplevel.transition
  val use_mltext: string -> theory option -> theory option
  val use_mltext_theory: string -> theory -> theory
  val use_setup: string -> theory -> theory
  val parse_ast_translation: string -> theory -> theory
  val parse_translation: string -> theory -> theory
  val print_translation: string -> theory -> theory
  val typed_print_translation: string -> theory -> theory
  val print_ast_translation: string -> theory -> theory
  val token_translation: string -> theory -> theory
  val add_oracle: (bstring * string) * Comment.text -> theory -> theory
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

(* formal comments *)

fun add_text comment thy = thy;
fun add_title title author date thy = thy;
val add_chapter = add_text;
val add_section = add_text;
val add_subsection = add_text;
val add_subsubsection = add_text;


(* signature and syntax *)

val add_classes = Theory.add_classes o Comment.ignore;
val add_classes_i = Theory.add_classes_i o Comment.ignore;
val add_classrel = Theory.add_classrel o single o Comment.ignore;
val add_classrel_i = Theory.add_classrel_i o single o Comment.ignore;
val add_defsort = Theory.add_defsort o Comment.ignore;
val add_defsort_i = Theory.add_defsort_i o Comment.ignore;
val add_nonterminals = Theory.add_nonterminals o map Comment.ignore;
val add_tyabbrs = Theory.add_tyabbrs o map Comment.ignore;
val add_tyabbrs_i = Theory.add_tyabbrs_i o map Comment.ignore;
val add_arities = Theory.add_arities o map Comment.ignore;
val add_arities_i = Theory.add_arities_i o map Comment.ignore;
val add_typedecl = PureThy.add_typedecls o single o Comment.ignore;
val add_consts = Theory.add_consts o map Comment.ignore;
val add_consts_i = Theory.add_consts_i o map Comment.ignore;
fun add_modesyntax mode = Theory.add_modesyntax mode o map Comment.ignore;
fun add_modesyntax_i mode = Theory.add_modesyntax_i mode o map Comment.ignore;
val add_trrules = Theory.add_trrules o map Comment.ignore;
val add_trrules_i = Theory.add_trrules_i o map Comment.ignore;



(* axioms and defs *)

fun add_axms f args thy =
  f (map (fn (x, srcs) => (x, map (Attrib.global_attribute thy) srcs)) args) thy;

val add_axioms = add_axms PureThy.add_axioms o map Comment.ignore;
val add_axioms_i = PureThy.add_axioms_i o map Comment.ignore;
val add_defs = add_axms PureThy.add_defs o map Comment.ignore;
val add_defs_i = PureThy.add_defs_i o map Comment.ignore;


(* constdefs *)

fun gen_add_constdefs consts defs args thy =
  thy
  |> consts (map (Comment.ignore o fst) args)
  |> defs (map (fn (((c, _, mx), _), (s, _)) =>
    (((Thm.def_name (Syntax.const_name c mx), s), []), Comment.none)) args);

fun add_constdefs args = gen_add_constdefs Theory.add_consts add_defs args;
fun add_constdefs_i args = gen_add_constdefs Theory.add_consts_i add_defs_i args;


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
val have_theorems = #1 oo (global_have_thmss (PureThy.have_thmss o Some) o Comment.ignore);
val have_theorems_i = #1 oo (have_thmss_i (PureThy.have_thmss o Some) o Comment.ignore);
val have_lemmas = #1 oo (global_have_thmss (have_lemss o Some) o Comment.ignore);
val have_lemmas_i = #1 oo (have_thmss_i (have_lemss o Some) o Comment.ignore);
val have_facts = ProofHistory.apply o local_have_thmss Proof.have_thmss o Comment.ignore;
val have_facts_i = ProofHistory.apply o have_thmss_i Proof.have_thmss o Comment.ignore;


(* forward chaining *)

fun gen_from_facts f = ProofHistory.apply o (Proof.chain oo curry (f Proof.have_thmss) ("", []));

val from_facts = gen_from_facts local_have_thmss o Comment.ignore;
val from_facts_i = gen_from_facts have_thmss_i o Comment.ignore;
fun chain comment_ignore = ProofHistory.apply Proof.chain;


(* context *)

val fix = ProofHistory.apply o Proof.fix o Comment.ignore;
val fix_i = ProofHistory.apply o Proof.fix_i o Comment.ignore;
val match_bind = ProofHistory.apply o Proof.match_bind o map Comment.ignore;
val match_bind_i = ProofHistory.apply o Proof.match_bind_i o map Comment.ignore;


(* statements *)

fun global_statement f (name, src, s) int thy =
  ProofHistory.init (Toplevel.undo_limit int)
    (f name (map (Attrib.global_attribute thy) src) s thy);

fun global_statement_i f (name, atts, t) int thy =
  ProofHistory.init (Toplevel.undo_limit int) (f name atts t thy);

fun local_statement do_open f g (name, src, s) = ProofHistory.apply_cond_open do_open (fn state =>
  f name (map (Attrib.local_attribute (Proof.theory_of state)) src) s (g state));

fun local_statement_i do_open f g (name, atts, t) =
  ProofHistory.apply_cond_open do_open (f name atts t o g);

val theorem   = global_statement Proof.theorem o Comment.ignore;
val theorem_i = global_statement_i Proof.theorem_i o Comment.ignore;
val lemma     = global_statement Proof.lemma o Comment.ignore;
val lemma_i   = global_statement_i Proof.lemma_i o Comment.ignore;
val assume    = local_statement false Proof.assume I o Comment.ignore;
val assume_i  = local_statement_i false Proof.assume_i I o Comment.ignore;
val show      = local_statement true Proof.show I o Comment.ignore;
val show_i    = local_statement_i true Proof.show_i I o Comment.ignore;
val have      = local_statement true Proof.have I o Comment.ignore;
val have_i    = local_statement_i true Proof.have_i I o Comment.ignore;
val thus      = local_statement true Proof.show Proof.chain o Comment.ignore;
val thus_i    = local_statement_i true Proof.show_i Proof.chain o Comment.ignore;
val hence     = local_statement true Proof.have Proof.chain o Comment.ignore;
val hence_i   = local_statement_i true Proof.have_i Proof.chain o Comment.ignore;


(* blocks *)

val begin_block = ProofHistory.apply_open Proof.begin_block;
val next_block = ProofHistory.apply Proof.next_block;
val end_block = ProofHistory.apply_close Proof.end_block;


(* backward steps *)

val tac = ProofHistory.applys o Method.tac;
val then_tac = ProofHistory.applys o Method.then_tac;

val proof =
  ProofHistory.applys o Method.proof o apsome Comment.ignore_interest o Comment.ignore_interest';


(* print result *)

fun pretty_result {kind, name, thm} =
  Pretty.block [Pretty.str (kind ^ " " ^ name ^ ":"), Pretty.fbrk, Display.pretty_thm thm];

val print_result = Pretty.writeln o pretty_result;
fun cond_print_result int res = if int then print_result res else ();

fun proof'' f = Toplevel.proof' (f o cond_print_result);


(* local endings *)

val local_qed =
  proof'' o (ProofHistory.applys_close oo Method.local_qed) o apsome Comment.ignore_interest;

val local_terminal_proof =
  proof'' o (ProofHistory.applys_close oo Method.local_terminal_proof) o Comment.ignore_interest;

val local_immediate_proof = proof'' (ProofHistory.applys_close o Method.local_immediate_proof);
val local_default_proof = proof'' (ProofHistory.applys_close o Method.local_default_proof);


(* global endings *)

val kill_proof = Proof.theory_of o ProofHistory.current;

fun global_result finish = Toplevel.proof_to_theory (fn prf =>
  let
    val state = ProofHistory.current prf;
    val _ = if Proof.at_bottom state then () else raise Toplevel.UNDEF;
    val (thy, res) = finish state;
  in print_result res; thy end);

fun gen_global_qed_with prep_att (alt_name, raw_atts) meth state =
  let
    val thy = Proof.theory_of state;
    val alt_atts = apsome (map (prep_att thy)) raw_atts;
  in Method.global_qed alt_name alt_atts (apsome Comment.ignore_interest meth) state end;

val global_qed_with = global_result oo gen_global_qed_with Attrib.global_attribute;
val global_qed_with_i = global_result oo gen_global_qed_with (K I);
val global_qed = global_qed_with (None, None);

val global_terminal_proof = global_result o Method.global_terminal_proof o Comment.ignore_interest;
val global_immediate_proof = global_result Method.global_immediate_proof;
val global_default_proof = global_result Method.global_default_proof;


(* common endings *)

fun qed meth = local_qed meth o global_qed meth;
fun terminal_proof meth = local_terminal_proof meth o global_terminal_proof meth;
val immediate_proof = local_immediate_proof o global_immediate_proof;
val default_proof = local_default_proof o global_default_proof;


(* calculational proof commands *)

fun cond_print_calc int thm =
  if int then Pretty.writeln (Pretty.big_list "calculation:" [Display.pretty_thm thm])
  else ();

fun proof''' f = Toplevel.proof' (f o cond_print_calc);

fun also _ = proof''' (ProofHistory.applys o Calculation.also);
fun finally _ = proof''' (ProofHistory.applys o Calculation.finally);


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

fun add_oracle ((name, txt), comment_ignore) =
  use_let
    "oracle: bstring * (Sign.sg * Object.T -> term)"
    "Theory.add_oracle oracle"
    ("(" ^ quote name ^ ", " ^ txt ^ ")");


(* theory init and exit *)

fun begin_theory name parents files =
  let
    val paths = map (apfst Path.unpack) files;
    val thy = ThyInfo.begin_theory name parents paths;
  in Present.begin_theory name parents paths thy end;

fun end_theory thy =
  (Present.end_theory (PureThy.get_name thy); ThyInfo.end_theory thy);

fun kill_theory thy = ThyInfo.remove_thy (PureThy.get_name thy);

fun bg_theory (name, parents, files) () = begin_theory name parents files;
fun en_theory thy = (end_theory thy; ());

fun theory spec = Toplevel.init_theory (bg_theory spec) en_theory kill_theory;


(* context switch *)

fun switch_theory load s =
  Toplevel.init_theory (fn () => (the (#2 (Context.pass None load s)))) (K ()) (K ());

val context = switch_theory ThyInfo.use_thy;
val update_context = switch_theory ThyInfo.update_thy;


end;
