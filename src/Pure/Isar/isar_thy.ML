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
  val add_defs: bool * (((bstring * string) * Args.src list) * Comment.text) list
    -> theory -> theory
  val add_defs_i: bool * (((bstring * term) * theory attribute list) * Comment.text) list
    -> theory -> theory
  val add_constdefs: (((bstring * string * mixfix) * Comment.text) * (string * Comment.text)) list
    -> theory -> theory
  val add_constdefs_i: (((bstring * typ * mixfix) * Comment.text) * (term * Comment.text)) list
    -> theory -> theory
  val apply_theorems: (xstring * Args.src list) list -> theory -> theory * thm list
  val apply_theorems_i: (thm * theory attribute list) list -> theory -> theory * thm list
  val declare_theorems: (xstring * Args.src list) list * Comment.text -> theory -> theory
  val declare_theorems_i: (thm * theory attribute list) list * Comment.text -> theory -> theory
  val have_theorems: string ->
    (((bstring * Args.src list) * (xstring * Args.src list) list) * Comment.text) list
    -> theory -> theory
  val have_theorems_i:  string ->
    (((bstring * theory attribute list) * (thm * theory attribute list) list)
    * Comment.text) list -> theory -> theory
  val have_facts: (((string * Args.src list) * (string * Args.src list) list) * Comment.text) list
    -> ProofHistory.T -> ProofHistory.T
  val have_facts_i: (((string * Proof.context attribute list) *
    (thm * Proof.context attribute list) list) * Comment.text) list
    -> ProofHistory.T -> ProofHistory.T
  val from_facts: ((string * Args.src list) list * Comment.text) list
    -> ProofHistory.T -> ProofHistory.T
  val from_facts_i: ((thm * Proof.context attribute list) list * Comment.text) list
    -> ProofHistory.T -> ProofHistory.T
  val with_facts: ((string * Args.src list) list * Comment.text) list
    -> ProofHistory.T -> ProofHistory.T
  val with_facts_i: ((thm * Proof.context attribute list) list * Comment.text) list
    -> ProofHistory.T -> ProofHistory.T
  val chain: Comment.text -> ProofHistory.T -> ProofHistory.T
  val fix: ((string list * string option) * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val fix_i: ((string list * typ option) * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val let_bind: ((string list * string) * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val let_bind_i: ((term list * term) * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val invoke_case: (string * string option list * Args.src list) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val invoke_case_i: (string * string option list * Proof.context attribute list) * Comment.text
    -> ProofHistory.T -> ProofHistory.T
  val theorem: string -> (xstring * Args.src list) option * Args.src Locale.element list
    -> ((bstring * Args.src list) * (string * (string list * string list))) * Comment.text
    -> bool -> theory -> ProofHistory.T
  val theorem_i: string -> (string * Proof.context attribute list) option
    * Proof.context attribute Locale.element_i list
    -> ((bstring * Theory.theory Thm.attribute list) *
      (Term.term * (Term.term list * Term.term list))) * Comment.text
    -> bool -> theory -> ProofHistory.T
  val multi_theorem: string -> (bstring * Args.src list)
    -> (xstring * Args.src list) option * Args.src Locale.element list
    -> (((bstring * Args.src list) * (string * (string list * string list)) list)
    * Comment.text) list -> bool -> theory -> ProofHistory.T
  val multi_theorem_i: string -> (bstring * theory attribute list)
    -> (string * Proof.context attribute list) option
      * Proof.context attribute Locale.element_i list ->
    (((bstring * Theory.theory Thm.attribute list) *
      (Term.term * (Term.term list * Term.term list)) list) * Comment.text) list
    -> bool -> theory -> ProofHistory.T
  val assume: (((string * Args.src list) * (string * (string list * string list)) list)
    * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val assume_i: (((string * Proof.context attribute list) * (term * (term list * term list)) list)
    * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val presume: (((string * Args.src list) * (string * (string list * string list)) list)
    * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val presume_i: (((string * Proof.context attribute list) * (term * (term list * term list)) list)
    * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val have: (((string * Args.src list) *
    (string * (string list * string list)) list) * Comment.text) list
    -> ProofHistory.T -> ProofHistory.T
  val have_i: (((string * Proof.context Thm.attribute list) *
    (Term.term * (Term.term list * Term.term list)) list) * Comment.text) list
    -> ProofHistory.T -> ProofHistory.T
  val hence: (((string * Args.src list) *
    (string * (string list * string list)) list) * Comment.text) list
    -> ProofHistory.T -> ProofHistory.T
  val hence_i: (((string * Proof.context Thm.attribute list) *
    (Term.term * (Term.term list * Term.term list)) list) * Comment.text) list
    -> ProofHistory.T -> ProofHistory.T
  val show: (((string * Args.src list) *
    (string * (string list * string list)) list) * Comment.text) list
    -> bool -> ProofHistory.T -> ProofHistory.T
  val show_i: (((string * Proof.context Thm.attribute list) *
    (Term.term * (Term.term list * Term.term list)) list) * Comment.text) list
    -> bool -> ProofHistory.T -> ProofHistory.T
  val thus: (((string * Args.src list) *
    (string * (string list * string list)) list) * Comment.text) list
    -> bool -> ProofHistory.T -> ProofHistory.T
  val thus_i: (((string * Proof.context Thm.attribute list) *
    (Term.term * (Term.term list * Term.term list)) list) * Comment.text) list
    -> bool -> ProofHistory.T -> ProofHistory.T
  val local_def: ((string * Args.src list) * (string * (string * string list)))
    * Comment.text -> ProofHistory.T -> ProofHistory.T
  val local_def_i: ((string * Args.src list) * (string * (term * term list)))
    * Comment.text -> ProofHistory.T -> ProofHistory.T
  val obtain: ((string list * string option) * Comment.text) list
    * (((string * Args.src list) * (string * (string list * string list)) list)
      * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val obtain_i: ((string list * typ option) * Comment.text) list
    * (((string * Proof.context attribute list) * (term * (term list * term list)) list)
      * Comment.text) list -> ProofHistory.T -> ProofHistory.T
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
  val parse_ast_translation: string * Comment.text -> theory -> theory
  val parse_translation: string * Comment.text -> theory -> theory
  val print_translation: string * Comment.text -> theory -> theory
  val typed_print_translation: string * Comment.text -> theory -> theory
  val print_ast_translation: string * Comment.text -> theory -> theory
  val token_translation: string * Comment.text -> theory -> theory
  val method_setup: (bstring * string * string) * Comment.text -> theory -> theory
  val add_oracle: (bstring * string) * Comment.text -> theory -> theory
  val add_locale: bstring * Locale.expr * (Args.src Locale.element * Comment.text) list
    -> theory -> theory
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
 [(Sign.classK, can o Sign.certify_class),
  (Sign.typeK, fn sg => fn c =>
    can (Sign.certify_tycon sg) c orelse can (Sign.certify_tyabbr sg) c),
  (Sign.constK, can o Sign.certify_const)];

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
val add_judgment = ObjectLogic.add_judgment o Comment.ignore;
val add_judgment_i = ObjectLogic.add_judgment_i o Comment.ignore;


(* axioms and defs *)

fun add_axms f args thy =
  f (map (fn (x, srcs) => (x, map (Attrib.global_attribute thy) srcs)) args) thy;

val add_axioms = add_axms (#1 oo PureThy.add_axioms) o map Comment.ignore;
val add_axioms_i = (#1 oo PureThy.add_axioms_i) o map Comment.ignore;
fun add_defs (x, args) = add_axms (#1 oo PureThy.add_defs x) (map Comment.ignore args);
fun add_defs_i (x, args) = (#1 oo PureThy.add_defs_i x) (map Comment.ignore args);


(* constdefs *)

fun gen_add_constdefs consts defs args thy =
  thy
  |> consts (map (Comment.ignore o fst) args)
  |> defs (false, map (fn (((c, _, mx), _), (s, _)) =>
    (((Thm.def_name (Syntax.const_name c mx), s), []), Comment.none)) args);

fun add_constdefs args = gen_add_constdefs Theory.add_consts add_defs args;
fun add_constdefs_i args = gen_add_constdefs Theory.add_consts_i add_defs_i args;


(* theorems *)

fun prep_thmss get attrib = map (fn ((name, more_srcs), th_srcs) =>
  ((name, map attrib more_srcs), map (fn (s, srcs) => (get s, map attrib srcs)) th_srcs));

fun flat_unnamed (x, ys) = (x, flat (map snd ys));
fun cond_kind k = if k = "" then [] else [Drule.kind k];

fun global_have_thmss kind f args thy =
  let
    val args' = prep_thmss (PureThy.get_thms thy) (Attrib.global_attribute thy) args
    val (thy', named_thmss) = f (cond_kind kind) args' thy;
    fun present (name, thms) = Present.results (kind ^ "s") name thms;
  in
    if kind = "" orelse kind = Drule.internalK then ()
    else Context.setmp (Some thy') (fn () => seq present named_thmss) ();
    (thy', named_thmss)
  end;

fun local_have_thmss f args state =
  let
    val args' = prep_thmss (ProofContext.get_thms (Proof.context_of state))
      (Attrib.local_attribute (Proof.theory_of state)) args;
  in f args' state end;

fun gen_have_thmss_i f args = f (map (fn ((name, more_atts), th_atts) =>
  ((name, more_atts), map (apfst single) th_atts)) args);

fun apply_theorems th_srcs =
  flat_unnamed o global_have_thmss "" PureThy.have_thmss [(("", []), th_srcs)];
fun apply_theorems_i th_srcs =
  flat_unnamed o gen_have_thmss_i (PureThy.have_thmss []) [(("", []), th_srcs)];

val declare_theorems = #1 oo (apply_theorems o Comment.ignore);
val declare_theorems_i = #1 oo (apply_theorems_i o Comment.ignore);

fun have_theorems kind =
  #1 oo (global_have_thmss kind PureThy.have_thmss o map Comment.ignore);
fun have_theorems_i kind =
  #1 oo (gen_have_thmss_i (PureThy.have_thmss (cond_kind kind)) o map Comment.ignore);

val have_facts = ProofHistory.apply o local_have_thmss Proof.have_thmss o map Comment.ignore;
val have_facts_i = ProofHistory.apply o gen_have_thmss_i Proof.have_thmss o map Comment.ignore;


(* forward chaining *)

fun gen_from_facts f args = ProofHistory.apply (Proof.chain o f (map (pair ("", [])) args));

val from_facts = gen_from_facts (local_have_thmss Proof.have_thmss) o map Comment.ignore;
val from_facts_i = gen_from_facts (gen_have_thmss_i Proof.have_thmss) o map Comment.ignore;
val with_facts = gen_from_facts (local_have_thmss Proof.with_thmss) o map Comment.ignore;
val with_facts_i = gen_from_facts (gen_have_thmss_i Proof.with_thmss) o map Comment.ignore;

fun chain comment_ignore = ProofHistory.apply Proof.chain;


(* context *)

val fix = ProofHistory.apply o Proof.fix o map Comment.ignore;
val fix_i = ProofHistory.apply o Proof.fix_i o map Comment.ignore;
val let_bind = ProofHistory.apply o Proof.let_bind o map Comment.ignore;
val let_bind_i = ProofHistory.apply o Proof.let_bind_i o map Comment.ignore;

fun invoke_case ((name, xs, src), comment_ignore) = ProofHistory.apply (fn state =>
  Proof.invoke_case (name, xs, map (Attrib.local_attribute (Proof.theory_of state)) src) state);
val invoke_case_i = ProofHistory.apply o Proof.invoke_case o Comment.ignore;


(* local results *)

local

fun prt_fact ctxt ("", ths) = ProofContext.pretty_thms ctxt ths
  | prt_fact ctxt (name, ths) =
      Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1, ProofContext.pretty_thms ctxt ths];

fun prt_facts ctxt =
  flat o (separate [Pretty.fbrk, Pretty.str "and "]) o map (single o prt_fact ctxt);

fun pretty_results ctxt ((kind, ""), facts) =
      Pretty.block (Pretty.str kind :: Pretty.brk 1 :: prt_facts ctxt facts)
  | pretty_results ctxt ((kind, name), facts) = Pretty.blk (1,
      [Pretty.str (kind ^ " " ^ name ^ ":"), Pretty.fbrk,
        Pretty.blk (1, Pretty.str "(" :: prt_facts ctxt facts @ [Pretty.str ")"])]);

fun pretty_rule s ctxt thm =
  Pretty.block [Pretty.str (s ^ " to solve goal by exported rule:"),
    Pretty.fbrk, ProofContext.pretty_thm ctxt thm];

in

val print_result = Pretty.writeln oo pretty_results;
fun print_result' ctxt (k, res) = print_result ctxt ((k, ""), res);

fun cond_print_result_rule int =
  if int then (print_result', priority oo (Pretty.string_of oo pretty_rule "Attempt"))
  else (K (K ()), K (K ()));

fun proof'' f = Toplevel.proof' (f o cond_print_result_rule);

fun check_goal false state = state
  | check_goal true state =
      let
        val rule = ref (None: thm option);
        fun warn exn =
          (["Problem! Local statement will fail to solve any pending goal"] @
          (case exn of None => [] | Some e => [Toplevel.exn_message e]) @
          (case ! rule of None => [] | Some thm =>
            [Pretty.string_of (pretty_rule "Failed attempt" (Proof.context_of state) thm)]))
          |> cat_lines |> warning;
        val check =
          (fn () => Seq.pull (SkipProof.local_skip_proof (K (K ()),
            fn _ => fn thm => rule := Some thm) true state))
          |> Library.setmp proofs 0
          |> Library.transform_error;
        val result = (check (), None) handle Interrupt => raise Interrupt | e => (None, Some e);
      in (case result of (Some _, None) => () | (_, exn) => warn exn); state end;

end;


(* statements *)

local

fun global_attributes thy ((name, src), s) = ((name, map (Attrib.global_attribute thy) src), s);

fun global_statement f args int thy =
  ProofHistory.init (Toplevel.undo_limit int) (f (map (global_attributes thy) args) thy);
fun global_statement_i f args int thy = ProofHistory.init (Toplevel.undo_limit int) (f args thy);

fun local_attributes state ((name, src), s) =
  ((name, map (Attrib.local_attribute (Proof.theory_of state)) src), s);

fun local_statement' f g args int = ProofHistory.apply (fn state =>
  f (map (local_attributes state) args) int (g state));
fun local_statement_i' f g args int = ProofHistory.apply (f args int o g);
fun local_statement f g args = local_statement' (K o f) g args ();
fun local_statement_i f g args = local_statement_i' (K o f) g args ();

in

fun multi_theorem k a (locale, elems) args int thy =
  global_statement (Proof.multi_theorem k (apsnd (map (Attrib.global_attribute thy)) a)
    (apsome (apsnd (map (Attrib.local_attribute thy))) locale)
    (map (Locale.attribute (Attrib.local_attribute thy)) elems)) (map Comment.ignore args) int thy;

fun multi_theorem_i k a (locale, elems) =
  global_statement_i (Proof.multi_theorem_i k a locale elems) o map Comment.ignore;

fun theorem k loc ((a, t), cmt) = multi_theorem k a loc [((("", []), [t]), cmt)];
fun theorem_i k loc ((a, t), cmt) = multi_theorem_i k a loc [((("", []), [t]), cmt)];

val assume      = local_statement Proof.assume I o map Comment.ignore;
val assume_i    = local_statement_i Proof.assume_i I o map Comment.ignore;
val presume     = local_statement Proof.presume I o map Comment.ignore;
val presume_i   = local_statement_i Proof.presume_i I o map Comment.ignore;
val have        = local_statement (Proof.have Seq.single) I o map Comment.ignore;
val have_i      = local_statement_i (Proof.have_i Seq.single) I o map Comment.ignore;
val hence       = local_statement (Proof.have Seq.single) Proof.chain o map Comment.ignore;
val hence_i     = local_statement_i (Proof.have_i Seq.single) Proof.chain o map Comment.ignore;
val show        = local_statement' (Proof.show check_goal Seq.single) I o map Comment.ignore;
val show_i      = local_statement_i' (Proof.show_i check_goal Seq.single) I o map Comment.ignore;
val thus = local_statement' (Proof.show check_goal Seq.single) Proof.chain o map Comment.ignore;
val thus_i = local_statement_i' (Proof.show_i check_goal Seq.single) Proof.chain o map Comment.ignore;

fun gen_def f ((name, srcs), def) = ProofHistory.apply (fn state =>
  f name (map (Attrib.local_attribute (Proof.theory_of state)) srcs) def state);

val local_def = gen_def Proof.def o Comment.ignore;
val local_def_i = gen_def Proof.def_i o Comment.ignore;

fun obtain (xs, asms) = ProofHistory.applys (fn state =>
  Obtain.obtain (map Comment.ignore xs)
    (map (local_attributes state) (map Comment.ignore asms)) state);

fun obtain_i (xs, asms) = ProofHistory.applys (fn state =>
  Obtain.obtain_i (map Comment.ignore xs) (map Comment.ignore asms) state);

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


(* local endings *)

val local_qed =
  proof'' o (ProofHistory.applys oo Method.local_qed true) o apsome Comment.ignore_interest;

fun ignore_interests (x, y) = (Comment.ignore_interest x, apsome Comment.ignore_interest y);

val local_terminal_proof =
  proof'' o (ProofHistory.applys oo Method.local_terminal_proof) o ignore_interests;

val local_default_proof = proof'' (ProofHistory.applys o Method.local_default_proof);
val local_immediate_proof = proof'' (ProofHistory.applys o Method.local_immediate_proof);
val local_done_proof = proof'' (ProofHistory.applys o Method.local_done_proof);
val local_skip_proof = Toplevel.proof' (fn int =>
  ProofHistory.applys (SkipProof.local_skip_proof (cond_print_result_rule int) int));


(* global endings *)

fun global_result finish = Toplevel.proof_to_theory' (fn int => fn prf =>
  let
    val state = ProofHistory.current prf;
    val _ = if Proof.at_bottom state then () else raise Toplevel.UNDEF;
    val (thy, ((kind, name), res)) = finish int state;
  in
    if kind = "" orelse kind = Drule.internalK then ()
    else (print_result (Proof.context_of state) ((kind, name), res);
      Context.setmp (Some thy) Present.multi_result (kind, res));
    thy
  end);

fun global_qed m = global_result (K (Method.global_qed true (apsome Comment.ignore_interest m)));
fun global_terminal_proof m =
  global_result (K (Method.global_terminal_proof (ignore_interests m)));
val global_default_proof = global_result (K Method.global_default_proof);
val global_immediate_proof = global_result (K Method.global_immediate_proof);
val global_skip_proof = global_result SkipProof.global_skip_proof;
val global_done_proof = global_result (K Method.global_done_proof);


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

fun cond_print_calc int ctxt thms =
  if int then
    Pretty.writeln (Pretty.big_list "calculation:" (map (ProofContext.pretty_thm ctxt) thms))
  else ();

fun proof''' f = Toplevel.proof' (f o cond_print_calc);

fun gen_calc get f (args, _) prt state =
  f (apsome (fn (srcs, _) => get srcs state) args) prt state;

in

fun get_thmss srcs = Proof.the_facts o local_have_thmss Proof.have_thmss [(("", []), srcs)];
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
  Context.use_let "val parse_ast_translation: (string * (Syntax.ast list -> Syntax.ast)) list"
    "Theory.add_trfuns (parse_ast_translation, [], [], [])" o Comment.ignore;

val parse_translation =
  Context.use_let "val parse_translation: (string * (term list -> term)) list"
    "Theory.add_trfuns ([], parse_translation, [], [])" o Comment.ignore;

val print_translation =
  Context.use_let "val print_translation: (string * (term list -> term)) list"
    "Theory.add_trfuns ([], [], print_translation, [])" o Comment.ignore;

val print_ast_translation =
  Context.use_let "val print_ast_translation: (string * (Syntax.ast list -> Syntax.ast)) list"
    "Theory.add_trfuns ([], [], [], print_ast_translation)" o Comment.ignore;

val typed_print_translation =
  Context.use_let "val typed_print_translation: (string * (bool -> typ -> term list -> term)) list"
    "Theory.add_trfunsT typed_print_translation" o Comment.ignore;

val token_translation =
  Context.use_let "val token_translation: (string * string * (string -> string * real)) list"
    "Theory.add_tokentrfuns token_translation" o Comment.ignore;


(* add method *)

fun method_setup ((name, txt, cmt), comment_ignore) =
  Context.use_let
    "val thm = PureThy.get_thm_closure (Context.the_context ());\n\
    \val thms = PureThy.get_thms_closure (Context.the_context ());\n\
    \val method: bstring * (Args.src -> Proof.context -> Proof.method) * string"
    "PureIsar.Method.add_method method"
    ("(" ^ quote name ^ ", " ^ txt ^ ", " ^ quote cmt ^ ")");


(* add_oracle *)

fun add_oracle ((name, txt), comment_ignore) =
  Context.use_let
    "val oracle: bstring * (Sign.sg * Object.T -> term)"
    "Theory.add_oracle oracle"
    ("(" ^ quote name ^ ", " ^ txt ^ ")");


(* add_locale *)

fun add_locale (name, imports, elems) thy =
  Locale.add_locale name imports
    (map (Locale.attribute (Attrib.local_attribute thy) o Comment.ignore) elems) thy;


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
