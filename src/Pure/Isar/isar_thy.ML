(*  Title:      Pure/Isar/isar_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Pure/Isar derived theory operations.
*)

signature ISAR_THY =
sig
  val add_header: Comment.text -> Toplevel.transition -> Toplevel.transition
  val add_chapter: Comment.text -> theory -> theory
  val add_section: Comment.text -> theory -> theory
  val add_subsection: Comment.text -> theory -> theory
  val add_subsubsection: Comment.text -> theory -> theory
  val add_text: Comment.text -> theory -> theory
  val add_text_raw: Comment.text -> theory -> theory
  val add_sect: Comment.text -> ProofHistory.T -> ProofHistory.T
  val add_subsect: Comment.text -> ProofHistory.T -> ProofHistory.T
  val add_subsubsect: Comment.text -> ProofHistory.T -> ProofHistory.T
  val add_txt: Comment.text -> ProofHistory.T -> ProofHistory.T
  val add_txt_raw: Comment.text -> ProofHistory.T -> ProofHistory.T
  val global_path: Comment.text -> theory -> theory
  val local_path: Comment.text -> theory -> theory
  val hide_space: (string * xstring list) * Comment.text -> theory -> theory
  val hide_space_i: (string * string list) * Comment.text -> theory -> theory
  val add_classes: (bclass * xclass list) list * Comment.text -> theory -> theory
  val add_classes_i: (bclass * class list) list * Comment.text  -> theory -> theory
  val add_classrel: (xclass * xclass) * Comment.text -> theory -> theory
  val add_classrel_i: (class * class) * Comment.text -> theory -> theory
  val add_defsort: string * Comment.text -> theory -> theory
  val add_defsort_i: sort * Comment.text -> theory -> theory
  val add_nonterminals: (bstring * Comment.text) list -> theory -> theory
  val add_tyabbrs: ((bstring * string list * string * mixfix) * Comment.text) list
    -> theory -> theory
  val add_tyabbrs_i: ((bstring * string list * typ * mixfix) * Comment.text) list
    -> theory -> theory
  val add_arities: ((xstring * string list * string) * Comment.text) list -> theory -> theory
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
  val add_judgment: (bstring * string * mixfix) * Comment.text -> theory -> theory
  val add_judgment_i: (bstring * typ * mixfix) * Comment.text -> theory -> theory
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
  val with_facts: (string * Args.src list) list * Comment.text -> ProofHistory.T -> ProofHistory.T
  val with_facts_i: (thm * Proof.context attribute list) list * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val chain: Comment.text -> ProofHistory.T -> ProofHistory.T
  val fix: ((string list * string option) * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val fix_i: ((string list * typ option) * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val let_bind: ((string list * string) * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val let_bind_i: ((term list * term) * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val invoke_case: (string * Args.src list) * Comment.text -> ProofHistory.T -> ProofHistory.T
  val invoke_case_i: (string * Proof.context attribute list) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val theorem: (bstring * Args.src list * (string * (string list * string list)))
    * Comment.text -> bool -> theory -> ProofHistory.T
  val theorem_i: (bstring * theory attribute list * (term * (term list * term list)))
    * Comment.text -> bool -> theory -> ProofHistory.T
  val lemma: (bstring * Args.src list * (string * (string list * string list)))
    * Comment.text -> bool -> theory -> ProofHistory.T
  val lemma_i: (bstring * theory attribute list * (term * (term list * term list)))
    * Comment.text -> bool -> theory -> ProofHistory.T
  val assume: ((string * Args.src list * (string * (string list * string list)) list)
    * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val assume_i: ((string * Proof.context attribute list * (term * (term list * term list)) list)
    * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val presume: ((string * Args.src list * (string * (string list * string list)) list)
    * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val presume_i: ((string * Proof.context attribute list * (term * (term list * term list)) list)
    * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val local_def: (string * Args.src list * ((string * string option) * (string * string list)))
    * Comment.text -> ProofHistory.T -> ProofHistory.T
  val local_def_i: (string * Args.src list * ((string * typ option) * (term * term list)))
    * Comment.text -> ProofHistory.T -> ProofHistory.T
  val show: (string * Args.src list * (string * (string list * string list)))
    * Comment.text -> ProofHistory.T -> ProofHistory.T
  val show_i: (string * Proof.context attribute list * (term * (term list * term list)))
    * Comment.text -> ProofHistory.T -> ProofHistory.T
  val have: (string * Args.src list * (string * (string list * string list)))
    * Comment.text -> ProofHistory.T -> ProofHistory.T
  val have_i: (string * Proof.context attribute list * (term * (term list * term list)))
    * Comment.text -> ProofHistory.T -> ProofHistory.T
  val thus: (string * Args.src list * (string * (string list * string list)))
    * Comment.text -> ProofHistory.T -> ProofHistory.T
  val thus_i: (string * Proof.context attribute list * (term * (term list * term list)))
    * Comment.text -> ProofHistory.T -> ProofHistory.T
  val hence: (string * Args.src list * (string * (string list * string list)))
    * Comment.text -> ProofHistory.T -> ProofHistory.T
  val hence_i: (string * Proof.context attribute list * (term * (term list * term list)))
    * Comment.text -> ProofHistory.T -> ProofHistory.T
  val begin_block: Comment.text -> ProofHistory.T -> ProofHistory.T
  val next_block: Comment.text -> ProofHistory.T -> ProofHistory.T
  val end_block: Comment.text -> ProofHistory.T -> ProofHistory.T
  val defer: int option * Comment.text -> ProofHistory.T -> ProofHistory.T
  val prefer: int * Comment.text -> ProofHistory.T -> ProofHistory.T
  val apply: Method.text * Comment.text -> ProofHistory.T -> ProofHistory.T
  val apply_end: Method.text * Comment.text -> ProofHistory.T -> ProofHistory.T
  val proof: (Comment.interest * (Method.text * Comment.interest) option) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val qed: (Method.text * Comment.interest) option * Comment.text
    -> Toplevel.transition -> Toplevel.transition
  val terminal_proof: ((Method.text * Comment.interest) * (Method.text * Comment.interest) option)
    * Comment.text -> Toplevel.transition -> Toplevel.transition
  val default_proof: Comment.text -> Toplevel.transition -> Toplevel.transition
  val immediate_proof: Comment.text -> Toplevel.transition -> Toplevel.transition
  val done_proof: Comment.text -> Toplevel.transition -> Toplevel.transition
  val skip_proof: Comment.text -> Toplevel.transition -> Toplevel.transition
  val forget_proof: Comment.text -> Toplevel.transition -> Toplevel.transition
  val get_thmss: (string * Args.src list) list -> Proof.state -> thm list
  val also: ((string * Args.src list) list * Comment.interest) option * Comment.text
    -> Toplevel.transition -> Toplevel.transition
  val also_i: (thm list * Comment.interest) option * Comment.text
    -> Toplevel.transition -> Toplevel.transition
  val finally: ((string * Args.src list) list * Comment.interest) option * Comment.text
    -> Toplevel.transition -> Toplevel.transition
  val finally_i: (thm list * Comment.interest) option * Comment.text
    -> Toplevel.transition -> Toplevel.transition
  val moreover: Comment.text -> Toplevel.transition -> Toplevel.transition
  val ultimately: Comment.text -> Toplevel.transition -> Toplevel.transition
  val parse_ast_translation: string -> theory -> theory
  val parse_translation: string -> theory -> theory
  val print_translation: string -> theory -> theory
  val typed_print_translation: string -> theory -> theory
  val print_ast_translation: string -> theory -> theory
  val token_translation: string -> theory -> theory
  val add_oracle: (bstring * string) * Comment.text -> theory -> theory
  val begin_theory: string -> string list -> (string * bool) list -> theory
  val end_theory: theory -> theory
  val kill_theory: string -> unit
  val theory: string * string list * (string * bool) list
    -> Toplevel.transition -> Toplevel.transition
  val init_context: ('a -> unit) -> 'a -> Toplevel.transition -> Toplevel.transition
  val context: string -> Toplevel.transition -> Toplevel.transition
end;

structure IsarThy: ISAR_THY =
struct


(** derived theory and proof operations **)

(* markup commands *)

fun add_header comment =
  Toplevel.keep (fn state => if Toplevel.is_toplevel state then () else raise Toplevel.UNDEF);

fun add_text _ x = x;
fun add_text_raw _ x = x;

fun add_heading add present txt thy =
  (Context.setmp (Some thy) present (Comment.string_of txt); add txt thy);

val add_chapter = add_heading add_text Present.section;
val add_section = add_heading add_text Present.section;
val add_subsection = add_heading add_text Present.subsection;
val add_subsubsection = add_heading add_text Present.subsubsection;

fun add_txt (_: Comment.text) = ProofHistory.apply I;
val add_txt_raw = add_txt;
val add_sect = add_txt;
val add_subsect = add_txt;
val add_subsubsect = add_txt;


(* name spaces *)

fun global_path comment_ignore = PureThy.global_path;
fun local_path comment_ignore = PureThy.local_path;

local

val kinds =
 [(Sign.classK, fn sg => fn c => c mem Sign.classes sg),
  (Sign.typeK, fn sg => fn c =>
    let val {tycons, abbrs, ...} = Type.rep_tsig (Sign.tsig_of sg)
    in is_some (Symtab.lookup (tycons, c)) orelse is_some (Symtab.lookup (abbrs, c)) end),
  (Sign.constK, is_some oo Sign.const_type)];

fun gen_hide intern ((kind, xnames), comment_ignore) thy =
  (case assoc (kinds, kind) of
    Some check =>
      let
        val sg = Theory.sign_of thy;
        val names = map (intern sg kind) xnames;
        val bads = filter_out (check sg) names;
      in
        if null bads then Theory.hide_space_i (kind, names) thy
        else error ("Attempt to hide undeclared item(s): " ^ commas_quote bads)
      end
  | None => error ("Bad name space specification: " ^ quote kind));

in

fun hide_space x = gen_hide Sign.intern x;
fun hide_space_i x = gen_hide (K (K I)) x;

end;


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
val add_judgment = AutoBind.add_judgment o Comment.ignore;
val add_judgment_i = AutoBind.add_judgment_i o Comment.ignore;


(* axioms and defs *)

fun add_axms f args thy =
  f (map (fn (x, srcs) => (x, map (Attrib.global_attribute thy) srcs)) args) thy;

val add_axioms = add_axms (#1 oo PureThy.add_axioms) o map Comment.ignore;
val add_axioms_i = (#1 oo PureThy.add_axioms_i) o map Comment.ignore;
val add_defs = add_axms (#1 oo PureThy.add_defs) o map Comment.ignore;
val add_defs_i = (#1 oo PureThy.add_defs_i) o map Comment.ignore;


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

fun global_have_thmss kind f (x as ((name, _), _)) thy =
  let val (thy', thms) = gen_have_thmss PureThy.get_thms Attrib.global_attribute f x thy in
    if kind <> "" then Context.setmp (Some thy') (Present.results kind name) thms else ();
    (thy', thms)
  end;

fun local_have_thmss x =
  gen_have_thmss (ProofContext.get_thms o Proof.context_of)
    (Attrib.local_attribute o Proof.theory_of) x;

fun gen_have_thmss_i f ((name, more_atts), th_atts) =
  f name more_atts (map (apfst single) th_atts);

fun have_lemss name atts = PureThy.have_thmss name (atts @ [Drule.tag_lemma]);


fun apply_theorems th_srcs = global_have_thmss "" PureThy.have_thmss (("", []), th_srcs);
fun apply_theorems_i th_srcs = gen_have_thmss_i PureThy.have_thmss (("", []), th_srcs);
val have_theorems = #1 oo (global_have_thmss "theorems" PureThy.have_thmss o Comment.ignore);
val have_theorems_i = #1 oo (gen_have_thmss_i PureThy.have_thmss o Comment.ignore);
val have_lemmas = #1 oo (global_have_thmss "lemmas" have_lemss o Comment.ignore);
val have_lemmas_i = #1 oo (gen_have_thmss_i have_lemss o Comment.ignore);
val have_facts = ProofHistory.apply o local_have_thmss (Proof.have_thmss []) o Comment.ignore;
val have_facts_i = ProofHistory.apply o gen_have_thmss_i (Proof.have_thmss []) o Comment.ignore;


(* forward chaining *)

fun gen_from_facts f = ProofHistory.apply o (Proof.chain oo curry f ("", []));

fun add_thmss name atts ths_atts state =
  Proof.have_thmss (Proof.the_facts state) name atts ths_atts state;

val from_facts = gen_from_facts (local_have_thmss (Proof.have_thmss [])) o Comment.ignore;
val from_facts_i = gen_from_facts (gen_have_thmss_i (Proof.have_thmss [])) o Comment.ignore;
val with_facts = gen_from_facts (local_have_thmss add_thmss) o Comment.ignore;
val with_facts_i = gen_from_facts (gen_have_thmss_i add_thmss) o Comment.ignore;

fun chain comment_ignore = ProofHistory.apply Proof.chain;


(* context *)

val fix = ProofHistory.apply o Proof.fix o map Comment.ignore;
val fix_i = ProofHistory.apply o Proof.fix_i o map Comment.ignore;
val let_bind = ProofHistory.apply o Proof.let_bind o map Comment.ignore;
val let_bind_i = ProofHistory.apply o Proof.let_bind_i o map Comment.ignore;

fun invoke_case ((name, src), comment_ignore) = ProofHistory.apply (fn state =>
  Proof.invoke_case (name, map (Attrib.local_attribute (Proof.theory_of state)) src) state);
val invoke_case_i = ProofHistory.apply o Proof.invoke_case o Comment.ignore;


(* statements *)

local

fun global_statement f (name, src, s) int thy =
  ProofHistory.init (Toplevel.undo_limit int)
    (f name (map (Attrib.global_attribute thy) src) s thy);

fun global_statement_i f (name, atts, t) int thy =
  ProofHistory.init (Toplevel.undo_limit int) (f name atts t thy);

fun local_statement f g (name, src, s) = ProofHistory.apply (fn state =>
  f name (map (Attrib.local_attribute (Proof.theory_of state)) src) s (g state));

fun local_statement_i f g (name, atts, t) = ProofHistory.apply (f name atts t o g);

fun multi_local_attribute state (name, src, s) =
  (name, map (Attrib.local_attribute (Proof.theory_of state)) src, s);

fun multi_statement f args = ProofHistory.apply (fn state =>
  f (map (multi_local_attribute state) args) state);

fun multi_statement_i f args = ProofHistory.apply (f args);

in

val theorem     = global_statement Proof.theorem o Comment.ignore;
val theorem_i   = global_statement_i Proof.theorem_i o Comment.ignore;
val lemma       = global_statement Proof.lemma o Comment.ignore;
val lemma_i     = global_statement_i Proof.lemma_i o Comment.ignore;
val assume      = multi_statement Proof.assume o map Comment.ignore;
val assume_i    = multi_statement_i Proof.assume_i o map Comment.ignore;
val presume     = multi_statement Proof.presume o map Comment.ignore;
val presume_i   = multi_statement_i Proof.presume_i o map Comment.ignore;
val local_def   = local_statement LocalDefs.def I o Comment.ignore;
val local_def_i = local_statement LocalDefs.def_i I o Comment.ignore;
val show        = local_statement (Proof.show Seq.single) I o Comment.ignore;
val show_i      = local_statement_i (Proof.show_i Seq.single) I o Comment.ignore;
val have        = local_statement (Proof.have Seq.single) I o Comment.ignore;
val have_i      = local_statement_i (Proof.have_i Seq.single) I o Comment.ignore;
val thus        = local_statement (Proof.show Seq.single) Proof.chain o Comment.ignore;
val thus_i      = local_statement_i (Proof.show_i Seq.single) Proof.chain o Comment.ignore;
val hence       = local_statement (Proof.have Seq.single) Proof.chain o Comment.ignore;
val hence_i     = local_statement_i (Proof.have_i Seq.single) Proof.chain o Comment.ignore;

end;


(* blocks *)

fun begin_block comment_ignore = ProofHistory.apply Proof.begin_block;
fun next_block comment_ignore = ProofHistory.apply Proof.next_block;
fun end_block comment_ignore = ProofHistory.applys Proof.end_block;


(* shuffle state *)

fun shuffle meth i = Method.refine (Method.Basic (K (meth i))) o Proof.assert_no_chain;

fun defer (i, comment_ignore) = ProofHistory.applys (shuffle Method.defer i);
fun prefer (i, comment_ignore) = ProofHistory.applys (shuffle Method.prefer i);


(* backward steps *)

fun apply (m, comment_ignore) = ProofHistory.applys
  (Seq.map (Proof.goal_facts (K [])) o Method.refine m o Proof.assert_backward);

fun apply_end (m, comment_ignore) = ProofHistory.applys
  (Method.refine_end m o Proof.assert_forward);

val proof = ProofHistory.applys o Method.proof o
  apsome Comment.ignore_interest o Comment.ignore_interest' o Comment.ignore;


(* print result *)

local

fun pretty_result {kind, name, thm} =
  Pretty.block [Pretty.str (kind ^ (if name = "" then "" else " " ^ name) ^ ":"),
    Pretty.fbrk, Proof.pretty_thm thm];

fun pretty_rule thm =
  Pretty.block [Pretty.str "trying to solve goal by rule:", Pretty.fbrk, Proof.pretty_thm thm];

in

val print_result = Pretty.writeln o pretty_result;

fun cond_print_result_rule int =
  if int then (print_result, Pretty.writeln o pretty_rule)
  else (K (), K ());

fun proof'' f = Toplevel.proof' (f o cond_print_result_rule);

end;


(* local endings *)

val local_qed =
  proof'' o (ProofHistory.applys oo Method.local_qed true) o apsome Comment.ignore_interest;

fun ignore_interests (x, y) = (Comment.ignore_interest x, apsome Comment.ignore_interest y);

val local_terminal_proof =
  proof'' o (ProofHistory.applys oo Method.local_terminal_proof) o ignore_interests;

val local_default_proof = proof'' (ProofHistory.applys o Method.local_default_proof);
val local_immediate_proof = proof'' (ProofHistory.applys o Method.local_immediate_proof);
val local_skip_proof = proof'' (ProofHistory.applys o SkipProof.local_skip_proof);
val local_done_proof = proof'' (ProofHistory.applys o Method.local_done_proof);


(* global endings *)

fun global_result finish = Toplevel.proof_to_theory (fn prf =>
  let
    val state = ProofHistory.current prf;
    val _ = if Proof.at_bottom state then () else raise Toplevel.UNDEF;
    val (thy, res as {kind, name, thm}) = finish state;
  in print_result res; Context.setmp (Some thy) (Present.result kind name) thm; thy end);

val global_qed = global_result o Method.global_qed true o apsome Comment.ignore_interest;
val global_terminal_proof = global_result o Method.global_terminal_proof o ignore_interests;
val global_default_proof = global_result Method.global_default_proof;
val global_immediate_proof = global_result Method.global_immediate_proof;
val global_skip_proof = global_result SkipProof.global_skip_proof;
val global_done_proof = global_result Method.global_done_proof;


(* common endings *)

fun qed (meth, comment) = local_qed meth o global_qed meth;
fun terminal_proof (meths, comment) = local_terminal_proof meths o global_terminal_proof meths;
fun default_proof comment = local_default_proof o global_default_proof;
fun immediate_proof comment = local_immediate_proof o global_immediate_proof;
fun done_proof comment = local_done_proof o global_done_proof;
fun skip_proof comment = local_skip_proof o global_skip_proof;

fun forget_proof comment = Toplevel.proof_to_theory (Proof.theory_of o ProofHistory.current);


(* calculational proof commands *)

local

fun cond_print_calc int thms =
  if int then Pretty.writeln (Pretty.big_list "calculation:" (map Proof.pretty_thm thms))
  else ();

fun proof''' f = Toplevel.proof' (f o cond_print_calc);

fun gen_calc get f (args, _) prt state =
  f (apsome (fn (srcs, _) => get srcs state) args) prt state;

in

fun get_thmss srcs = Proof.the_facts o local_have_thmss (Proof.have_thmss []) (("", []), srcs); 
fun get_thmss_i thms _ = thms;

fun also x = proof''' (ProofHistory.applys o gen_calc get_thmss Calculation.also x);
fun also_i x = proof''' (ProofHistory.applys o gen_calc get_thmss_i Calculation.also x);
fun finally x = proof''' (ProofHistory.applys o gen_calc get_thmss Calculation.finally x);
fun finally_i x = proof''' (ProofHistory.applys o gen_calc get_thmss_i Calculation.finally x);
fun moreover comment = proof''' (ProofHistory.apply o Calculation.moreover);
fun ultimately comment = proof''' (ProofHistory.apply o Calculation.ultimately);

end;


(* translation functions *)

val parse_ast_translation =
  Context.use_let "parse_ast_translation: (string * (Syntax.ast list -> Syntax.ast)) list"
    "Theory.add_trfuns (parse_ast_translation, [], [], [])";

val parse_translation =
  Context.use_let "parse_translation: (string * (term list -> term)) list"
    "Theory.add_trfuns ([], parse_translation, [], [])";

val print_translation =
  Context.use_let "print_translation: (string * (term list -> term)) list"
    "Theory.add_trfuns ([], [], print_translation, [])";

val print_ast_translation =
  Context.use_let "print_ast_translation: (string * (Syntax.ast list -> Syntax.ast)) list"
    "Theory.add_trfuns ([], [], [], print_ast_translation)";

val typed_print_translation =
  Context.use_let "typed_print_translation: (string * (bool -> typ -> term list -> term)) list"
    "Theory.add_trfunsT typed_print_translation";

val token_translation =
  Context.use_let "token_translation: (string * string * (string -> string * int)) list"
    "Theory.add_tokentrfuns token_translation";


(* add_oracle *)

fun add_oracle ((name, txt), comment_ignore) =
  Context.use_let
    "oracle: bstring * (Sign.sg * Object.T -> term)"
    "Theory.add_oracle oracle"
    ("(" ^ quote name ^ ", " ^ txt ^ ")");


(* theory init and exit *)

fun gen_begin_theory upd name parents files =
  ThyInfo.begin_theory Present.begin_theory upd name parents (map (apfst Path.unpack) files);

val begin_theory = gen_begin_theory false;

fun end_theory thy =
  if ThyInfo.check_known_thy (PureThy.get_name thy) then ThyInfo.end_theory thy
  else thy;

val kill_theory = ThyInfo.if_known_thy ThyInfo.remove_thy;


fun bg_theory (name, parents, files) int = gen_begin_theory int name parents files;
fun en_theory thy = (end_theory thy; ());

fun theory spec = Toplevel.init_theory (bg_theory spec) en_theory (kill_theory o PureThy.get_name);


(* context switch *)

fun fetch_context f x =
  (case Context.pass None f x of
    ((), None) => raise Toplevel.UNDEF
  | ((), Some thy) => thy);

fun init_context f x = Toplevel.init_theory (fn _ => fetch_context f x) (K ()) (K ());

val context = init_context (ThyInfo.quiet_update_thy true);


end;
