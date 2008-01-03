(*  Title:      Pure/Isar/isar_cmd.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Derived Isar commands.
*)

signature ISAR_CMD =
sig
  val generic_setup: string option -> theory -> theory
  val parse_ast_translation: bool * string -> theory -> theory
  val parse_translation: bool * string -> theory -> theory
  val print_translation: bool * string -> theory -> theory
  val typed_print_translation: bool * string -> theory -> theory
  val print_ast_translation: bool * string -> theory -> theory
  val token_translation: string -> theory -> theory
  val oracle: bstring -> string -> string -> theory -> theory
  val add_axioms: ((bstring * string) * Attrib.src list) list -> theory -> theory
  val add_defs: (bool * bool) * ((bstring * string) * Attrib.src list) list -> theory -> theory
  val apply_theorems: (thmref * Attrib.src list) list -> theory -> thm list * theory
  val apply_theorems_i: (thm list * attribute list) list -> theory -> thm list * theory
  val declaration: string -> local_theory -> local_theory
  val simproc_setup: string -> string list -> string -> string list -> local_theory -> local_theory
  val have: ((string * Attrib.src list) * (string * string list) list) list ->
    bool -> Proof.state -> Proof.state
  val hence: ((string * Attrib.src list) * (string * string list) list) list ->
    bool -> Proof.state -> Proof.state
  val show: ((string * Attrib.src list) * (string * string list) list) list ->
    bool -> Proof.state -> Proof.state
  val thus: ((string * Attrib.src list) * (string * string list) list) list ->
    bool -> Proof.state -> Proof.state
  val qed: Method.text option -> Toplevel.transition -> Toplevel.transition
  val terminal_proof: Method.text * Method.text option ->
    Toplevel.transition -> Toplevel.transition
  val default_proof: Toplevel.transition -> Toplevel.transition
  val immediate_proof: Toplevel.transition -> Toplevel.transition
  val done_proof: Toplevel.transition -> Toplevel.transition
  val skip_proof: Toplevel.transition -> Toplevel.transition
  val begin_theory: string -> string list -> (string * bool) list -> bool -> theory
  val end_theory: theory -> theory
  val kill_theory: string -> unit
  val theory: string * string list * (string * bool) list
    -> Toplevel.transition -> Toplevel.transition
  val welcome: Toplevel.transition -> Toplevel.transition
  val init_toplevel: Toplevel.transition -> Toplevel.transition
  val exit: Toplevel.transition -> Toplevel.transition
  val quit: Toplevel.transition -> Toplevel.transition
  val touch_child_thys: string -> Toplevel.transition -> Toplevel.transition
  val touch_thy: string -> Toplevel.transition -> Toplevel.transition
  val remove_thy: string -> Toplevel.transition -> Toplevel.transition
  val kill_thy: string -> Toplevel.transition -> Toplevel.transition
  val pr: string list * (int option * int option) -> Toplevel.transition -> Toplevel.transition
  val disable_pr: Toplevel.transition -> Toplevel.transition
  val enable_pr: Toplevel.transition -> Toplevel.transition
  val redo: Toplevel.transition -> Toplevel.transition
  val undos_proof: int -> Toplevel.transition -> Toplevel.transition
  val kill_proof_notify: (unit -> unit) -> Toplevel.transition -> Toplevel.transition
  val kill_proof: Toplevel.transition -> Toplevel.transition
  val undo_theory: Toplevel.transition -> Toplevel.transition
  val undo: Toplevel.transition -> Toplevel.transition
  val cannot_undo: string -> Toplevel.transition -> Toplevel.transition
  val kill: Toplevel.transition -> Toplevel.transition
  val back: Toplevel.transition -> Toplevel.transition
  val use: Path.T -> Toplevel.transition -> Toplevel.transition
  val use_mltext_theory: string -> Toplevel.transition -> Toplevel.transition
  val use_mltext: bool -> string -> Toplevel.transition -> Toplevel.transition
  val use_commit: Toplevel.transition -> Toplevel.transition
  val nested_command: Markup.property list -> string * Position.T -> Toplevel.transition
  val cd: Path.T -> Toplevel.transition -> Toplevel.transition
  val pwd: Toplevel.transition -> Toplevel.transition
  val use_thy: string -> Toplevel.transition -> Toplevel.transition
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
  val print_locale: bool * (Locale.expr * Element.context list)
    -> Toplevel.transition -> Toplevel.transition
  val print_registrations: bool -> string -> Toplevel.transition -> Toplevel.transition
  val print_attributes: Toplevel.transition -> Toplevel.transition
  val print_simpset: Toplevel.transition -> Toplevel.transition
  val print_rules: Toplevel.transition -> Toplevel.transition
  val print_trans_rules: Toplevel.transition -> Toplevel.transition
  val print_methods: Toplevel.transition -> Toplevel.transition
  val print_antiquotations: Toplevel.transition -> Toplevel.transition
  val class_deps: Toplevel.transition -> Toplevel.transition
  val thy_deps: Toplevel.transition -> Toplevel.transition
  val thm_deps: (thmref * Attrib.src list) list -> Toplevel.transition -> Toplevel.transition
  val find_theorems: (int option * bool) * (bool * string FindTheorems.criterion) list
    -> Toplevel.transition -> Toplevel.transition
  val print_binds: Toplevel.transition -> Toplevel.transition
  val print_cases: Toplevel.transition -> Toplevel.transition
  val print_stmts: string list * (thmref * Attrib.src list) list
    -> Toplevel.transition -> Toplevel.transition
  val print_thms: string list * (thmref * Attrib.src list) list
    -> Toplevel.transition -> Toplevel.transition
  val print_prfs: bool -> string list * (thmref * Attrib.src list) list option
    -> Toplevel.transition -> Toplevel.transition
  val print_prop: (string list * string) -> Toplevel.transition -> Toplevel.transition
  val print_term: (string list * string) -> Toplevel.transition -> Toplevel.transition
  val print_type: (string list * string) -> Toplevel.transition -> Toplevel.transition
  val add_header: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_chapter: xstring option * (string * Position.T) ->
    Toplevel.transition -> Toplevel.transition
  val add_section: xstring option * (string * Position.T) ->
    Toplevel.transition -> Toplevel.transition
  val add_subsection: xstring option * (string * Position.T) ->
    Toplevel.transition -> Toplevel.transition
  val add_subsubsection: xstring option * (string * Position.T) ->
    Toplevel.transition -> Toplevel.transition
  val add_text: xstring option * (string * Position.T) ->
    Toplevel.transition -> Toplevel.transition
  val add_text_raw: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_sect: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_subsect: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_subsubsect: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_txt: string * Position.T -> Toplevel.transition -> Toplevel.transition
  val add_txt_raw: string * Position.T -> Toplevel.transition -> Toplevel.transition
end;

structure IsarCmd: ISAR_CMD =
struct


(** theory declarations **)

(* generic_setup *)

fun generic_setup NONE = (fn thy => thy |> Context.setup ())
  | generic_setup (SOME txt) =
      ML_Context.use_let "val setup: theory -> theory" "Context.map_theory setup" txt
      |> Context.theory_map;


(* translation functions *)

local

fun advancedT false = ""
  | advancedT true = "Proof.context -> ";

fun advancedN false = ""
  | advancedN true = "advanced_";

in

fun parse_ast_translation (a, txt) =
  txt |> ML_Context.use_let ("val parse_ast_translation: (string * (" ^ advancedT a ^
      "Syntax.ast list -> Syntax.ast)) list")
    ("Context.map_theory (Sign.add_" ^ advancedN a ^ "trfuns (parse_ast_translation, [], [], []))")
  |> Context.theory_map;

fun parse_translation (a, txt) =
  txt |> ML_Context.use_let ("val parse_translation: (string * (" ^ advancedT a ^
      "term list -> term)) list")
    ("Context.map_theory (Sign.add_" ^ advancedN a ^ "trfuns ([], parse_translation, [], []))")
  |> Context.theory_map;

fun print_translation (a, txt) =
  txt |> ML_Context.use_let ("val print_translation: (string * (" ^ advancedT a ^
      "term list -> term)) list")
    ("Context.map_theory (Sign.add_" ^ advancedN a ^ "trfuns ([], [], print_translation, []))")
  |> Context.theory_map;

fun print_ast_translation (a, txt) =
  txt |> ML_Context.use_let ("val print_ast_translation: (string * (" ^ advancedT a ^
      "Syntax.ast list -> Syntax.ast)) list")
    ("Context.map_theory (Sign.add_" ^ advancedN a ^ "trfuns ([], [], [], print_ast_translation))")
  |> Context.theory_map;

fun typed_print_translation (a, txt) =
  txt |> ML_Context.use_let ("val typed_print_translation: (string * (" ^ advancedT a ^
      "bool -> typ -> term list -> term)) list")
    ("Context.map_theory (Sign.add_" ^ advancedN a ^ "trfunsT typed_print_translation)")
  |> Context.theory_map;

val token_translation =
  ML_Context.use_let "val token_translation: (string * string * (string -> output * int)) list"
    "Context.map_theory (Sign.add_tokentrfuns token_translation)"
  #> Context.theory_map;

end;


(* oracles *)

fun oracle name typ oracle =
  let val txt =
    "local\n\
    \  type T = " ^ typ ^ ";\n\
    \  val oracle: theory -> T -> term = " ^ oracle ^ ";\n\
    \  val name = " ^ quote name ^ ";\n\
    \  exception Arg of T;\n\
    \  val _ = ML_Context.>> (Theory.add_oracle (name, fn (thy, Arg x) => oracle thy x));\n\
    \  val thy = ML_Context.the_context ();\n\
    \  val invoke_" ^ name ^ " = Thm.invoke_oracle_i thy (Sign.full_name thy name);\n\
    \in\n\
    \  fun " ^ name ^ " thy x = invoke_" ^ name ^ " (thy, Arg x);\n\
    \end;\n";
  in ML_Context.use_mltext_update txt false end
  |> Context.theory_map;


(* axioms *)

fun add_axms f args thy =
  f (map (fn (x, srcs) => (x, map (Attrib.attribute thy) srcs)) args) thy;

val add_axioms = add_axms (snd oo PureThy.add_axioms);

fun add_defs ((unchecked, overloaded), args) =
  add_axms
    (snd oo (if unchecked then PureThy.add_defs_unchecked else PureThy.add_defs) overloaded) args;


(* facts *)

fun apply_theorems args thy =
  let val facts = Attrib.map_facts (Attrib.attribute thy) [(("", []), args)]
  in apfst (maps snd) (PureThy.note_thmss "" facts thy) end;

fun apply_theorems_i args = apfst (maps snd) o PureThy.note_thmss_i "" [(("", []), args)];


(* declarations *)

val declaration =
  ML_Context.use_let "val declaration: Morphism.declaration"
    "Context.map_proof (LocalTheory.declaration declaration)"
  #> Context.proof_map;


(* simprocs *)

fun simproc_setup name lhss proc identifier =
  ML_Context.use_let
    "val proc: Morphism.morphism -> Simplifier.simpset -> cterm -> thm option"
  ("Context.map_proof (Simplifier.def_simproc {name = " ^ ML_Syntax.print_string name ^ ", \
    \lhss = " ^ ML_Syntax.print_strings lhss ^ ", proc = proc, \
    \identifier = Library.maps ML_Context.thms " ^ ML_Syntax.print_strings identifier ^ "})") proc
  |> Context.proof_map;


(* goals *)

fun goal opt_chain goal stmt int =
  opt_chain #> goal NONE (K Seq.single) stmt int;

val have = goal I Proof.have;
val hence = goal Proof.chain Proof.have;
val show = goal I Proof.show;
val thus = goal Proof.chain Proof.show;


(* local endings *)

fun local_qed m = Toplevel.proofs (Proof.local_qed (m, true));
val local_terminal_proof = Toplevel.proofs o Proof.local_terminal_proof;
val local_default_proof = Toplevel.proofs Proof.local_default_proof;
val local_immediate_proof = Toplevel.proofs Proof.local_immediate_proof;
val local_done_proof = Toplevel.proofs Proof.local_done_proof;
val local_skip_proof = Toplevel.proofs' Proof.local_skip_proof;

val skip_local_qed =
  Toplevel.skip_proof (History.apply (fn i => if i > 1 then i - 1 else raise Toplevel.UNDEF));


(* global endings *)

fun global_qed m = Toplevel.end_proof (K (Proof.global_qed (m, true)));
val global_terminal_proof = Toplevel.end_proof o K o Proof.global_terminal_proof;
val global_default_proof = Toplevel.end_proof (K Proof.global_default_proof);
val global_immediate_proof = Toplevel.end_proof (K Proof.global_immediate_proof);
val global_skip_proof = Toplevel.end_proof Proof.global_skip_proof;
val global_done_proof = Toplevel.end_proof (K Proof.global_done_proof);

val skip_global_qed = Toplevel.skip_proof_to_theory (equal 1);


(* common endings *)

fun qed m = local_qed m o global_qed m o skip_local_qed o skip_global_qed;
fun terminal_proof m = local_terminal_proof m o global_terminal_proof m;
val default_proof = local_default_proof o global_default_proof;
val immediate_proof = local_immediate_proof o global_immediate_proof;
val done_proof = local_done_proof o global_done_proof;
val skip_proof = local_skip_proof o global_skip_proof;


(* init and exit *)

fun begin_theory name imports uses =
  ThyInfo.begin_theory name imports (map (apfst Path.explode) uses);

fun end_theory thy =
  if ThyInfo.check_known_thy (Context.theory_name thy) then ThyInfo.end_theory thy else thy;

val kill_theory = ThyInfo.if_known_thy ThyInfo.remove_thy;

fun theory (name, imports, uses) =
  Toplevel.init_theory (begin_theory name imports uses)
    (fn thy => (end_theory thy; ()))
    (kill_theory o Context.theory_name);

val init_toplevel = Toplevel.imperative (fn () => raise Toplevel.RESTART);

val welcome = Toplevel.imperative (writeln o Session.welcome);

val exit = Toplevel.keep (fn state =>
 (CRITICAL (fn () => ML_Context.set_context (try Toplevel.generic_theory_of state));
  raise Toplevel.TERMINATE));

val quit = Toplevel.imperative quit;


(* touch theories *)

fun touch_child_thys name = Toplevel.imperative (fn () => ThyInfo.touch_child_thys name);
fun touch_thy name = Toplevel.imperative (fn () => ThyInfo.touch_thy name);
fun remove_thy name = Toplevel.imperative (fn () => ThyInfo.remove_thy name);
fun kill_thy name = Toplevel.imperative (fn () => kill_theory name);


(* print state *)

fun set_limit _ NONE = ()
  | set_limit r (SOME n) = r := n;

fun pr (modes, (lim1, lim2)) = Toplevel.keep (fn state =>
  (set_limit goals_limit lim1; set_limit ProofContext.prems_limit lim2; Toplevel.quiet := false;
    PrintMode.with_modes modes (Toplevel.print_state true) state));

val disable_pr = Toplevel.imperative (fn () => Toplevel.quiet := true);
val enable_pr = Toplevel.imperative (fn () => Toplevel.quiet := false);


(* history commands *)

val redo =
  Toplevel.history History.redo o
  Toplevel.actual_proof ProofHistory.redo o
  Toplevel.skip_proof History.redo;

fun undos_proof n =
  Toplevel.actual_proof (fn prf =>
    if ProofHistory.is_initial prf then raise Toplevel.UNDEF else funpow n ProofHistory.undo prf) o
  Toplevel.skip_proof (fn h =>
    if History.is_initial h then raise Toplevel.UNDEF else funpow n History.undo h);

fun kill_proof_notify (f: unit -> unit) = Toplevel.history (fn hist =>
  if is_some (Toplevel.theory_node (History.current hist)) then raise Toplevel.UNDEF
  else (f (); History.undo hist));

val kill_proof = kill_proof_notify (K ());

val undo_theory = Toplevel.history (fn hist =>
  if History.is_initial hist then raise Toplevel.UNDEF else History.undo hist);

val undo = Toplevel.kill o undo_theory o Toplevel.undo_exit o undos_proof 1;

fun cannot_undo "end" = undo   (*ProofGeneral legacy*)
  | cannot_undo txt = Toplevel.imperative (fn () => error ("Cannot undo " ^ quote txt));

val kill = Toplevel.kill o kill_proof;

val back =
  Toplevel.actual_proof ProofHistory.back o
  Toplevel.skip_proof (History.apply I);


(* use ML text *)

fun use path = Toplevel.keep (fn state =>
  ML_Context.setmp (try Toplevel.generic_theory_of state) (ThyInfo.load_file false) path);

(*passes changes of theory context*)
val use_mltext_theory = Toplevel.theory' o (Context.theory_map oo ML_Context.use_mltext_update);

(*ignore result theory context*)
fun use_mltext v txt = Toplevel.keep' (fn verb => fn state =>
  (ML_Context.use_mltext txt (v andalso verb) (try Toplevel.generic_theory_of state)));

val use_commit = Toplevel.imperative Secure.commit;


(* nested commands *)

fun nested_command props (str, pos) =
  let val pos' = Position.of_properties (props @ Position.properties_of pos) in
    (case OuterSyntax.parse pos' str of
      [transition] => Toplevel.properties props transition
    | _ => error "exactly one command expected")
  end;


(* current working directory *)

fun cd path = Toplevel.imperative (fn () => (File.cd path));
val pwd = Toplevel.imperative (fn () => writeln (Path.implode (File.pwd ())));


(* load theory files *)

fun use_thy name = Toplevel.imperative (fn () => ML_Context.save ThyInfo.use_thy name);


(* present draft files *)

fun display_drafts files = Toplevel.imperative (fn () =>
  let val outfile = File.shell_path (Present.drafts (getenv "ISABELLE_DOC_FORMAT") files)
  in File.isatool ("display -c " ^ outfile ^ " &"); () end);

fun print_drafts files = Toplevel.imperative (fn () =>
  let val outfile = File.shell_path (Present.drafts "ps" files)
  in File.isatool ("print -c " ^ outfile); () end);


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
  (case Option.map Toplevel.theory_node (History.previous (Toplevel.node_history_of state)) of
    SOME (SOME prev_thy) => ProofDisplay.print_theorems_diff (Context.theory_of prev_thy)
  | _ => ProofDisplay.print_theorems));

val print_theorems = Toplevel.unknown_context o print_theorems_theory o print_theorems_proof;

val print_locales = Toplevel.unknown_theory o
  Toplevel.keep (Locale.print_locales o Toplevel.theory_of);

fun print_locale (show_facts, (imports, body)) = Toplevel.unknown_theory o
  Toplevel.keep (fn state =>
    Locale.print_locale (Toplevel.theory_of state) show_facts imports body);

fun print_registrations show_wits name = Toplevel.unknown_context o
  Toplevel.keep (Toplevel.node_case
      (Context.cases (Locale.print_registrations show_wits name o ProofContext.init)
        (Locale.print_registrations show_wits name))
    (Locale.print_registrations show_wits name o Proof.context_of));

val print_attributes = Toplevel.unknown_theory o
  Toplevel.keep (Attrib.print_attributes o Toplevel.theory_of);

val print_simpset = Toplevel.unknown_context o
  Toplevel.keep (Toplevel.node_case
    (Context.cases Simplifier.print_simpset Simplifier.print_local_simpset)
    (Simplifier.print_local_simpset o Proof.context_of));

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


(* retrieve theorems *)

fun thm_deps args = Toplevel.unknown_theory o Toplevel.keep (fn state =>
  ThmDeps.thm_deps (Proof.get_thmss (Toplevel.enter_proof_body state) args));

fun find_theorems ((opt_lim, rem_dups), spec) =
  Toplevel.unknown_theory o Toplevel.keep (fn state =>
  let
    val proof_state = Toplevel.enter_proof_body state;
    val ctxt = Proof.context_of proof_state;
    val opt_goal = try Proof.get_goal proof_state |> Option.map (Thm.prop_of o #2 o #2);
  in FindTheorems.print_theorems ctxt opt_goal opt_lim rem_dups spec end);


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
          val {thy, der = (_, prf), ...} = Thm.rep_thm thm;
          val prop = Thm.full_prop_of thm;
          val prf' = Proofterm.rewrite_proof_notypes ([], []) prf
        in
          ProofContext.pretty_proof ctxt
            (if full then Reconstruct.reconstruct_proof thy prop prf' else prf')
        end
    | SOME args => Pretty.chunks
        (map (ProofContext.pretty_proof_of (Proof.context_of state) full)
          (Proof.get_thmss state args)));

fun string_of_prop state s =
  let
    val ctxt = Proof.context_of state;
    val prop = Syntax.read_prop ctxt s;
  in Pretty.string_of (Pretty.quote (Syntax.pretty_term ctxt prop)) end;

fun string_of_term state s =
  let
    val ctxt = Proof.context_of state;
    val t = Syntax.read_term ctxt s;
    val T = Term.type_of t;
  in
    Pretty.string_of
      (Pretty.block [Pretty.quote (Syntax.pretty_term ctxt t), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt T)])
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

fun add_header s = Toplevel.keep' (fn int => fn state =>
  (if Toplevel.is_toplevel state then () else raise Toplevel.UNDEF;
   if int then OuterSyntax.check_text s NONE else ()));

local

fun present _ txt true node = OuterSyntax.check_text txt (SOME node)
  | present f (s, _) false node =
      ML_Context.setmp (try (Toplevel.cases_node I (Context.Proof o Proof.context_of)) node) f s;

fun present_local_theory f (loc, txt) = Toplevel.present_local_theory loc (present f txt);
fun present_proof f txt = Toplevel.print o Toplevel.present_proof (present f txt);

in

val add_chapter       = present_local_theory Present.section;
val add_section       = present_local_theory Present.section;
val add_subsection    = present_local_theory Present.subsection;
val add_subsubsection = present_local_theory Present.subsubsection;
val add_text          = present_local_theory (K ());
fun add_text_raw txt  = present_local_theory (K ()) (NONE, txt);
val add_txt           = present_proof (K ());
val add_txt_raw       = add_txt;
val add_sect          = add_txt;
val add_subsect       = add_txt;
val add_subsubsect    = add_txt;

end;

end;
