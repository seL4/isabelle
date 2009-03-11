(*  Title:      Pure/Isar/isar_cmd.ML
    Author:     Markus Wenzel, TU Muenchen

Derived Isar commands.
*)

signature ISAR_CMD =
sig
  val global_setup: string * Position.T -> theory -> theory
  val local_setup: string * Position.T -> Proof.context -> Proof.context
  val parse_ast_translation: bool * (string * Position.T) -> theory -> theory
  val parse_translation: bool * (string * Position.T) -> theory -> theory
  val print_translation: bool * (string * Position.T) -> theory -> theory
  val typed_print_translation: bool * (string * Position.T) -> theory -> theory
  val print_ast_translation: bool * (string * Position.T) -> theory -> theory
  val oracle: bstring * Position.T -> SymbolPos.text * Position.T -> theory -> theory
  val add_axioms: ((binding * string) * Attrib.src list) list -> theory -> theory
  val add_defs: (bool * bool) * ((binding * string) * Attrib.src list) list -> theory -> theory
  val declaration: string * Position.T -> local_theory -> local_theory
  val simproc_setup: string -> string list -> string * Position.T -> string list ->
    local_theory -> local_theory
  val hide_names: bool -> string * xstring list -> theory -> theory
  val have: (Attrib.binding * (string * string list) list) list -> bool -> Proof.state -> Proof.state
  val hence: (Attrib.binding * (string * string list) list) list -> bool -> Proof.state -> Proof.state
  val show: (Attrib.binding * (string * string list) list) list -> bool -> Proof.state -> Proof.state
  val thus: (Attrib.binding * (string * string list) list) list -> bool -> Proof.state -> Proof.state
  val qed: Method.text option -> Toplevel.transition -> Toplevel.transition
  val terminal_proof: Method.text * Method.text option ->
    Toplevel.transition -> Toplevel.transition
  val default_proof: Toplevel.transition -> Toplevel.transition
  val immediate_proof: Toplevel.transition -> Toplevel.transition
  val done_proof: Toplevel.transition -> Toplevel.transition
  val skip_proof: Toplevel.transition -> Toplevel.transition
  val init_theory: string * string list * (string * bool) list ->
    Toplevel.transition -> Toplevel.transition
  val exit: Toplevel.transition -> Toplevel.transition
  val quit: Toplevel.transition -> Toplevel.transition
  val pr: string list * (int option * int option) -> Toplevel.transition -> Toplevel.transition
  val disable_pr: Toplevel.transition -> Toplevel.transition
  val enable_pr: Toplevel.transition -> Toplevel.transition
  val ml_diag: bool -> string * Position.T -> Toplevel.transition -> Toplevel.transition
  val cd: Path.T -> Toplevel.transition -> Toplevel.transition
  val pwd: Toplevel.transition -> Toplevel.transition
  val display_drafts: Path.T list -> Toplevel.transition -> Toplevel.transition
  val print_drafts: Path.T list -> Toplevel.transition -> Toplevel.transition
  val pretty_setmargin: int -> Toplevel.transition -> Toplevel.transition
  val print_context: Toplevel.transition -> Toplevel.transition
  val print_theory: bool -> Toplevel.transition -> Toplevel.transition
  val print_syntax: Toplevel.transition -> Toplevel.transition
  val print_abbrevs: Toplevel.transition -> Toplevel.transition
  val print_facts: Toplevel.transition -> Toplevel.transition
  val print_configs: Toplevel.transition -> Toplevel.transition
  val print_theorems: Toplevel.transition -> Toplevel.transition
  val print_locales: Toplevel.transition -> Toplevel.transition
  val print_locale: bool * xstring -> Toplevel.transition -> Toplevel.transition
  val print_attributes: Toplevel.transition -> Toplevel.transition
  val print_simpset: Toplevel.transition -> Toplevel.transition
  val print_rules: Toplevel.transition -> Toplevel.transition
  val print_trans_rules: Toplevel.transition -> Toplevel.transition
  val print_methods: Toplevel.transition -> Toplevel.transition
  val print_antiquotations: Toplevel.transition -> Toplevel.transition
  val class_deps: Toplevel.transition -> Toplevel.transition
  val thy_deps: Toplevel.transition -> Toplevel.transition
  val thm_deps: (Facts.ref * Attrib.src list) list -> Toplevel.transition -> Toplevel.transition
  val unused_thms: (string list * string list option) option ->
    Toplevel.transition -> Toplevel.transition
  val print_binds: Toplevel.transition -> Toplevel.transition
  val print_cases: Toplevel.transition -> Toplevel.transition
  val print_stmts: string list * (Facts.ref * Attrib.src list) list
    -> Toplevel.transition -> Toplevel.transition
  val print_thms: string list * (Facts.ref * Attrib.src list) list
    -> Toplevel.transition -> Toplevel.transition
  val print_prfs: bool -> string list * (Facts.ref * Attrib.src list) list option
    -> Toplevel.transition -> Toplevel.transition
  val print_prop: (string list * string) -> Toplevel.transition -> Toplevel.transition
  val print_term: (string list * string) -> Toplevel.transition -> Toplevel.transition
  val print_type: (string list * string) -> Toplevel.transition -> Toplevel.transition
  val header_markup: SymbolPos.text * Position.T -> Toplevel.transition -> Toplevel.transition
  val local_theory_markup: xstring option * (SymbolPos.text * Position.T) ->
    Toplevel.transition -> Toplevel.transition
  val proof_markup: SymbolPos.text * Position.T -> Toplevel.transition -> Toplevel.transition
end;

structure IsarCmd: ISAR_CMD =
struct


(** theory declarations **)

(* generic setup *)

fun global_setup (txt, pos) =
  ML_Context.expression pos "val setup: theory -> theory" "Context.map_theory setup" txt
  |> Context.theory_map;

fun local_setup (txt, pos) =
  ML_Context.expression pos "val setup: local_theory -> local_theory" "Context.map_proof setup" txt
  |> Context.proof_map;


(* translation functions *)

local

fun advancedT false = ""
  | advancedT true = "Proof.context -> ";

fun advancedN false = ""
  | advancedN true = "advanced_";

in

fun parse_ast_translation (a, (txt, pos)) =
  txt |> ML_Context.expression pos
    ("val parse_ast_translation: (string * (" ^ advancedT a ^
      "Syntax.ast list -> Syntax.ast)) list")
    ("Context.map_theory (Sign.add_" ^ advancedN a ^ "trfuns (parse_ast_translation, [], [], []))")
  |> Context.theory_map;

fun parse_translation (a, (txt, pos)) =
  txt |> ML_Context.expression pos
    ("val parse_translation: (string * (" ^ advancedT a ^
      "term list -> term)) list")
    ("Context.map_theory (Sign.add_" ^ advancedN a ^ "trfuns ([], parse_translation, [], []))")
  |> Context.theory_map;

fun print_translation (a, (txt, pos)) =
  txt |> ML_Context.expression pos
    ("val print_translation: (string * (" ^ advancedT a ^
      "term list -> term)) list")
    ("Context.map_theory (Sign.add_" ^ advancedN a ^ "trfuns ([], [], print_translation, []))")
  |> Context.theory_map;

fun print_ast_translation (a, (txt, pos)) =
  txt |> ML_Context.expression pos
    ("val print_ast_translation: (string * (" ^ advancedT a ^
      "Syntax.ast list -> Syntax.ast)) list")
    ("Context.map_theory (Sign.add_" ^ advancedN a ^ "trfuns ([], [], [], print_ast_translation))")
  |> Context.theory_map;

fun typed_print_translation (a, (txt, pos)) =
  txt |> ML_Context.expression pos
    ("val typed_print_translation: (string * (" ^ advancedT a ^
      "bool -> typ -> term list -> term)) list")
    ("Context.map_theory (Sign.add_" ^ advancedN a ^ "trfunsT typed_print_translation)")
  |> Context.theory_map;

end;


(* oracles *)

fun oracle (name, pos) (body_txt, body_pos) =
  let
    val body = SymbolPos.content (SymbolPos.explode (body_txt, body_pos));
    val txt =
      "local\n\
      \  val name = " ^ ML_Syntax.print_string name ^ ";\n\
      \  val pos = " ^ ML_Syntax.print_position pos ^ ";\n\
      \  val binding = Binding.make (name, pos);\n\
      \  val body = " ^ body ^ ";\n\
      \in\n\
      \  val " ^ name ^ " = snd (Context.>>> (Context.map_theory_result (Thm.add_oracle (binding, body))));\n\
      \end;\n";
  in Context.theory_map (ML_Context.exec (fn () => ML_Context.eval false body_pos txt)) end;


(* axioms *)

fun add_axms f args thy =
  f (map (fn ((b, ax), srcs) => ((b, ax), map (Attrib.attribute thy) srcs)) args) thy;

val add_axioms = add_axms (snd oo PureThy.add_axioms_cmd);

fun add_defs ((unchecked, overloaded), args) =
  add_axms
    (snd oo (if unchecked then PureThy.add_defs_unchecked_cmd else PureThy.add_defs_cmd) overloaded) args;


(* declarations *)

fun declaration (txt, pos) =
  txt |> ML_Context.expression pos
    "val declaration: Morphism.declaration"
    "Context.map_proof (LocalTheory.declaration declaration)"
  |> Context.proof_map;


(* simprocs *)

fun simproc_setup name lhss (proc, pos) identifier =
  ML_Context.expression pos
    "val proc: Morphism.morphism -> Simplifier.simpset -> cterm -> thm option"
  ("Context.map_proof (Simplifier.def_simproc {name = " ^ ML_Syntax.print_string name ^ ", \
    \lhss = " ^ ML_Syntax.print_strings lhss ^ ", proc = proc, \
    \identifier = Library.maps ML_Context.thms " ^ ML_Syntax.print_strings identifier ^ "})") proc
  |> Context.proof_map;


(* hide names *)

val hide_kinds =
 [("class", (Sign.intern_class, can o Sign.certify_class, Sign.hide_class)),
  ("type", (Sign.intern_type, Sign.declared_tyname, Sign.hide_type)),
  ("const", (Sign.intern_const, Sign.declared_const, Sign.hide_const)),
  ("fact", (PureThy.intern_fact, PureThy.defined_fact, PureThy.hide_fact))];

fun hide_names b (kind, xnames) thy =
  (case AList.lookup (op =) hide_kinds kind of
    SOME (intern, check, hide) =>
      let
        val names = map (intern thy) xnames;
        val bads = filter_out (check thy) names;
      in
        if null bads then fold (hide b) names thy
        else error ("Attempt to hide undeclared item(s): " ^ commas_quote bads)
      end
  | NONE => error ("Bad name space specification: " ^ quote kind));


(* goals *)

fun goal opt_chain goal stmt int =
  opt_chain #> goal NONE (K I) stmt int;

val have = goal I Proof.have;
val hence = goal Proof.chain Proof.have;
val show = goal I Proof.show;
val thus = goal Proof.chain Proof.show;


(* local endings *)

fun local_qed m = Toplevel.proof (Proof.local_qed (m, true));
val local_terminal_proof = Toplevel.proof o Proof.local_terminal_proof;
val local_default_proof = Toplevel.proof Proof.local_default_proof;
val local_immediate_proof = Toplevel.proof Proof.local_immediate_proof;
val local_done_proof = Toplevel.proof Proof.local_done_proof;
val local_skip_proof = Toplevel.proof' Proof.local_skip_proof;

val skip_local_qed = Toplevel.skip_proof (fn i => if i > 1 then i - 1 else raise Toplevel.UNDEF);


(* global endings *)

fun global_qed m = Toplevel.end_proof (K (Proof.global_qed (m, true)));
val global_terminal_proof = Toplevel.end_proof o K o Proof.global_terminal_proof;
val global_default_proof = Toplevel.end_proof (K Proof.global_default_proof);
val global_immediate_proof = Toplevel.end_proof (K Proof.global_immediate_proof);
val global_skip_proof = Toplevel.end_proof Proof.global_skip_proof;
val global_done_proof = Toplevel.end_proof (K Proof.global_done_proof);

val skip_global_qed = Toplevel.skip_proof_to_theory (fn n => n = 1);


(* common endings *)

fun qed m = local_qed m o global_qed m o skip_local_qed o skip_global_qed;
fun terminal_proof m = local_terminal_proof m o global_terminal_proof m;
val default_proof = local_default_proof o global_default_proof;
val immediate_proof = local_immediate_proof o global_immediate_proof;
val done_proof = local_done_proof o global_done_proof;
val skip_proof = local_skip_proof o global_skip_proof;


(* init and exit *)

fun init_theory (name, imports, uses) =
  Toplevel.init_theory name (ThyInfo.begin_theory name imports (map (apfst Path.explode) uses))
    (fn thy =>
      if ThyInfo.check_known_thy (Context.theory_name thy)
      then ThyInfo.end_theory thy else ());

val exit = Toplevel.keep (fn state =>
 (Context.set_thread_data (try Toplevel.generic_theory_of state);
  raise Toplevel.TERMINATE));

val quit = Toplevel.imperative quit;


(* print state *)

fun set_limit _ NONE = ()
  | set_limit r (SOME n) = r := n;

fun pr (modes, (lim1, lim2)) = Toplevel.keep (fn state =>
  (set_limit goals_limit lim1; set_limit ProofContext.prems_limit lim2; Toplevel.quiet := false;
    PrintMode.with_modes modes (Toplevel.print_state true) state));

val disable_pr = Toplevel.imperative (fn () => Toplevel.quiet := true);
val enable_pr = Toplevel.imperative (fn () => Toplevel.quiet := false);


(* diagnostic ML evaluation *)

fun ml_diag verbose (txt, pos) = Toplevel.keep (fn state =>
  (ML_Context.eval_in
    (Option.map Context.proof_of (try Toplevel.generic_theory_of state)) verbose pos txt));


(* current working directory *)

fun cd path = Toplevel.imperative (fn () => (File.cd path));
val pwd = Toplevel.imperative (fn () => writeln (Path.implode (File.pwd ())));


(* present draft files *)

fun display_drafts files = Toplevel.imperative (fn () =>
  let val outfile = File.shell_path (Present.drafts (getenv "ISABELLE_DOC_FORMAT") files)
  in File.isabelle_tool ("display -c " ^ outfile ^ " &"); () end);

fun print_drafts files = Toplevel.imperative (fn () =>
  let val outfile = File.shell_path (Present.drafts "ps" files)
  in File.isabelle_tool ("print -c " ^ outfile); () end);


(* pretty_setmargin *)

fun pretty_setmargin n = Toplevel.imperative (fn () => Pretty.setmargin n);


(* print parts of theory and proof context *)

val print_context = Toplevel.keep Toplevel.print_state_context;

fun print_theory verbose = Toplevel.unknown_theory o
  Toplevel.keep (Pretty.writeln o ProofDisplay.pretty_full_theory verbose o Toplevel.theory_of);

val print_syntax = Toplevel.unknown_context o
  Toplevel.keep (ProofContext.print_syntax o Toplevel.context_of);

val print_abbrevs = Toplevel.unknown_context o
  Toplevel.keep (ProofContext.print_abbrevs o Toplevel.context_of);

val print_facts = Toplevel.unknown_context o Toplevel.keep (fn state =>
  ProofContext.setmp_verbose
    ProofContext.print_lthms (Toplevel.context_of state));

val print_configs = Toplevel.unknown_context o Toplevel.keep (fn state =>
  Attrib.print_configs (Toplevel.context_of state));

val print_theorems_proof = Toplevel.keep (fn state =>
  ProofContext.setmp_verbose
    ProofContext.print_lthms (Proof.context_of (Toplevel.proof_of state)));

val print_theorems_theory = Toplevel.keep (fn state =>
  Toplevel.theory_of state |>
  (case Toplevel.previous_node_of state of
    SOME prev_node =>
      ProofDisplay.print_theorems_diff (ProofContext.theory_of (Toplevel.context_node prev_node))
  | _ => ProofDisplay.print_theorems));

val print_theorems = Toplevel.unknown_context o print_theorems_theory o print_theorems_proof;

val print_locales = Toplevel.unknown_theory o
  Toplevel.keep (Locale.print_locales o Toplevel.theory_of);

fun print_locale (show_facts, name) = Toplevel.unknown_theory o
  Toplevel.keep (fn state =>
    Locale.print_locale (Toplevel.theory_of state) show_facts name);

val print_attributes = Toplevel.unknown_theory o
  Toplevel.keep (Attrib.print_attributes o Toplevel.theory_of);

val print_simpset = Toplevel.unknown_context o
  Toplevel.keep (fn state =>
    let val ctxt = Toplevel.context_of state
    in Pretty.writeln (Simplifier.pretty_ss ctxt (Simplifier.local_simpset_of ctxt)) end);

val print_rules = Toplevel.unknown_context o
  Toplevel.keep (ContextRules.print_rules o Toplevel.context_of);

val print_trans_rules = Toplevel.unknown_context o
  Toplevel.keep (Calculation.print_rules o Toplevel.context_of);

val print_methods = Toplevel.unknown_theory o
  Toplevel.keep (Method.print_methods o Toplevel.theory_of);

val print_antiquotations = Toplevel.imperative ThyOutput.print_antiquotations;

val thy_deps = Toplevel.unknown_theory o Toplevel.keep (fn state =>
  let
    val thy = Toplevel.theory_of state;
    val all_thys = sort ThyInfo.thy_ord (thy :: Theory.ancestors_of thy);
    val gr = all_thys |> map (fn node =>
      let
        val name = Context.theory_name node;
        val parents = map Context.theory_name (Theory.parents_of node);
        val dir = Present.session_name node;
        val unfold = not (ThyInfo.known_thy name andalso ThyInfo.is_finished name);
      in {name = name, ID = name, parents = parents, dir = dir, unfold = unfold, path = ""} end);
  in Present.display_graph gr end);

val class_deps = Toplevel.unknown_theory o Toplevel.keep (fn state =>
  let
    val thy = Toplevel.theory_of state;
    val {classes = (space, algebra), ...} = Type.rep_tsig (Sign.tsig_of thy);
    val {classes, ...} = Sorts.rep_algebra algebra;
    fun entry (c, (i, (_, cs))) =
      (i, {name = NameSpace.extern space c, ID = c, parents = cs,
            dir = "", unfold = true, path = ""});
    val gr =
      Graph.fold (cons o entry) classes []
      |> sort (int_ord o pairself #1) |> map #2;
  in Present.display_graph gr end);

fun thm_deps args = Toplevel.unknown_theory o Toplevel.keep (fn state =>
  ThmDeps.thm_deps (Proof.get_thmss (Toplevel.enter_proof_body state) args));


(* find unused theorems *)

fun unused_thms opt_range = Toplevel.keep (fn state =>
  let
    val thy = Toplevel.theory_of state;
    val ctxt = Toplevel.context_of state;
    fun pretty_thm (a, th) = ProofContext.pretty_fact ctxt (a, [th]);
  in
    ThmDeps.unused_thms
      (case opt_range of
        NONE => (Theory.parents_of thy, [thy])
      | SOME (xs, NONE) => (map ThyInfo.get_theory xs, [thy])
      | SOME (xs, SOME ys) => (map ThyInfo.get_theory xs, map ThyInfo.get_theory ys))
    |> map pretty_thm |> Pretty.chunks |> Pretty.writeln
  end);


(* print proof context contents *)

val print_binds = Toplevel.unknown_context o Toplevel.keep (fn state =>
  ProofContext.setmp_verbose ProofContext.print_binds (Toplevel.context_of state));

val print_cases = Toplevel.unknown_context o Toplevel.keep (fn state =>
  ProofContext.setmp_verbose ProofContext.print_cases (Toplevel.context_of state));


(* print theorems, terms, types etc. *)

local

fun string_of_stmts state args =
  Proof.get_thmss state args
  |> map (Element.pretty_statement (Proof.context_of state) Thm.theoremK)
  |> Pretty.chunks2 |> Pretty.string_of;

fun string_of_thms state args =
  Pretty.string_of (ProofContext.pretty_thms (Proof.context_of state)
    (Proof.get_thmss state args));

fun string_of_prfs full state arg =
  Pretty.string_of (case arg of
      NONE =>
        let
          val (ctxt, (_, thm)) = Proof.get_goal state;
          val thy = ProofContext.theory_of ctxt;
          val prf = Thm.proof_of thm;
          val prop = Thm.full_prop_of thm;
          val prf' = Proofterm.rewrite_proof_notypes ([], []) prf
        in
          ProofSyntax.pretty_proof ctxt
            (if full then Reconstruct.reconstruct_proof thy prop prf' else prf')
        end
    | SOME args => Pretty.chunks
        (map (ProofSyntax.pretty_proof_of (Proof.context_of state) full)
          (Proof.get_thmss state args)));

fun string_of_prop state s =
  let
    val ctxt = Proof.context_of state;
    val prop = Syntax.read_prop ctxt s;
    val ctxt' = Variable.auto_fixes prop ctxt;
  in Pretty.string_of (Pretty.quote (Syntax.pretty_term ctxt' prop)) end;

fun string_of_term state s =
  let
    val ctxt = Proof.context_of state;
    val t = Syntax.read_term ctxt s;
    val T = Term.type_of t;
    val ctxt' = Variable.auto_fixes t ctxt;
  in
    Pretty.string_of
      (Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' T)])
  end;

fun string_of_type state s =
  let
    val ctxt = Proof.context_of state;
    val T = Syntax.read_typ ctxt s;
  in Pretty.string_of (Pretty.quote (Syntax.pretty_typ ctxt T)) end;

fun print_item string_of (modes, arg) = Toplevel.keep (fn state =>
  PrintMode.with_modes modes (fn () =>
    writeln (string_of (Toplevel.enter_proof_body state) arg)) ());

in

val print_stmts = print_item string_of_stmts;
val print_thms = print_item string_of_thms;
val print_prfs = print_item o string_of_prfs;
val print_prop = print_item string_of_prop;
val print_term = print_item string_of_term;
val print_type = print_item string_of_type;

end;


(* markup commands *)

fun check_text (txt, pos) state =
 (Position.report Markup.doc_source pos;
  ignore (ThyOutput.eval_antiquote (#1 (OuterKeyword.get_lexicons ())) state (txt, pos)));

fun header_markup txt = Toplevel.keep (fn state =>
  if Toplevel.is_toplevel state then check_text txt state
  else raise Toplevel.UNDEF);

fun local_theory_markup (loc, txt) = Toplevel.present_local_theory loc (check_text txt);
val proof_markup = Toplevel.present_proof o check_text;

end;
