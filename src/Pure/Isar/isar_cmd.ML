(*  Title:      Pure/Isar/isar_cmd.ML
    Author:     Makarius

Miscellaneous Isar commands.
*)

signature ISAR_CMD =
sig
  val setup: Input.source -> theory -> theory
  val local_setup: Input.source -> Proof.context -> Proof.context
  val parse_ast_translation: Input.source -> theory -> theory
  val parse_translation: Input.source -> theory -> theory
  val print_translation: Input.source -> theory -> theory
  val typed_print_translation: Input.source -> theory -> theory
  val print_ast_translation: Input.source -> theory -> theory
  val translations: bool -> (string * string) Syntax.trrule list -> theory -> theory
  val syntax_consts: ((string * Position.T) list * (xstring * Position.T) list) list ->
    local_theory -> local_theory
  val syntax_types: ((string * Position.T) list * (xstring * Position.T) list) list ->
    local_theory -> local_theory
  val oracle: bstring * Position.range -> Input.source -> theory -> theory
  val declaration: {syntax: bool, pervasive: bool} -> Input.source -> local_theory -> local_theory
  val qed: Method.text_range option -> Toplevel.transition -> Toplevel.transition
  val terminal_proof: Method.text_range * Method.text_range option ->
    Toplevel.transition -> Toplevel.transition
  val default_proof: Toplevel.transition -> Toplevel.transition
  val immediate_proof: Toplevel.transition -> Toplevel.transition
  val done_proof: Toplevel.transition -> Toplevel.transition
  val skip_proof: Toplevel.transition -> Toplevel.transition
  val ml_diag: bool -> Input.source -> Toplevel.transition -> Toplevel.transition
  val diag_state: Proof.context -> Toplevel.state
  val diag_goal: Proof.context -> {context: Proof.context, facts: thm list, goal: thm}
  val pretty_theorems: bool -> Toplevel.state -> Pretty.T list
  val print_stmts: string list * (Facts.ref * Token.src list) list
    -> Toplevel.transition -> Toplevel.transition
  val print_thms: string list * (Facts.ref * Token.src list) list
    -> Toplevel.transition -> Toplevel.transition
  val print_prfs: bool -> string list * (Facts.ref * Token.src list) list option
    -> Toplevel.transition -> Toplevel.transition
  val print_prop: (string list * string) -> Toplevel.transition -> Toplevel.transition
  val print_term: (string list * string) -> Toplevel.transition -> Toplevel.transition
  val print_type: (string list * (string * string option)) ->
    Toplevel.transition -> Toplevel.transition
end;

structure Isar_Cmd: ISAR_CMD =
struct


(** theory declarations **)

(* generic setup *)

fun setup source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (" @ ML_Lex.read_source source @ ML_Lex.read ")")
  |> Context.theory_map;

fun local_setup source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.local_setup (" @ ML_Lex.read_source source @ ML_Lex.read ")")
  |> Context.proof_map;


(* translation functions *)

fun parse_ast_translation source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (Sign.parse_ast_translation (" @
      ML_Lex.read_source source @ ML_Lex.read "))")
  |> Context.theory_map;

fun parse_translation source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (Sign.parse_translation (" @
      ML_Lex.read_source source @ ML_Lex.read "))")
  |> Context.theory_map;

fun print_translation source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (Sign.print_translation (" @
      ML_Lex.read_source source @ ML_Lex.read "))")
  |> Context.theory_map;

fun typed_print_translation source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (Sign.typed_print_translation (" @
      ML_Lex.read_source source @ ML_Lex.read "))")
  |> Context.theory_map;

fun print_ast_translation source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (Sign.print_ast_translation (" @
      ML_Lex.read_source source @ ML_Lex.read "))")
  |> Context.theory_map;


(* translation rules *)

fun translations add raw_rules thy =
  let
    val thy_ctxt = Proof_Context.init_global thy;
    val rules = map (Syntax.parse_trrule thy_ctxt) raw_rules;
  in Sign.translations_global add rules thy end;


(* syntax consts/types (after translation) *)

local

fun syntax_deps_cmd f args lthy =
  let
    val check_lhs = Proof_Context.check_syntax_const lthy;
    fun check_rhs (b: xstring, pos: Position.T) =
      let
        val (c: string, reports) = f lthy (b, pos);
        val _ = Context_Position.reports lthy reports;
      in c end;

    fun check (raw_lhs, raw_rhs) =
      let
        val lhs = map check_lhs raw_lhs;
        val rhs = map check_rhs raw_rhs;
      in map (fn l => (l, rhs)) lhs end;
  in Local_Theory.syntax_deps (maps check args) lthy end;

fun check_const ctxt (s, pos) =
  Proof_Context.check_const {proper = true, strict = false} ctxt (s, [pos])
  |>> (Term.dest_Const_name #> Lexicon.mark_const #> tap (Sign.check_syntax_dep ctxt));

fun check_type_name ctxt arg =
  Proof_Context.check_type_name {proper = true, strict = false} ctxt arg
  |>> (Term.dest_Type_name #> Lexicon.mark_type #> tap (Sign.check_syntax_dep ctxt));

in

val syntax_consts = syntax_deps_cmd check_const;
val syntax_types = syntax_deps_cmd check_type_name;

end;


(* oracles *)

fun oracle (name, range) source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "val " @
     ML_Lex.read_range range name @
     ML_Lex.read
      (" = snd (Theory.setup_result (Thm.add_oracle (" ^
        ML_Syntax.make_binding (name, #1 range) ^ ", ") @
     ML_Lex.read_source source @ ML_Lex.read ")))")
  |> Context.theory_map;


(* declarations *)

fun declaration {syntax, pervasive} source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read
      ("Theory.local_setup (Local_Theory.declaration {syntax = " ^
        Bool.toString syntax ^ ", pervasive = " ^ Bool.toString pervasive ^
        ", pos = " ^ ML_Syntax.print_position (Position.thread_data ()) ^ "} (") @
     ML_Lex.read_source source @ ML_Lex.read "))")
  |> Context.proof_map;


(* local endings *)

fun local_qed m = Toplevel.proof (Proof.local_qed (m, true));
val local_terminal_proof = Toplevel.proof o Proof.local_future_terminal_proof;
val local_default_proof = Toplevel.proof Proof.local_default_proof;
val local_immediate_proof = Toplevel.proof Proof.local_immediate_proof;
val local_done_proof = Toplevel.proof Proof.local_done_proof;
val local_skip_proof = Toplevel.proof' Proof.local_skip_proof;


(* global endings *)

fun global_qed m = Toplevel.end_proof (K (Proof.global_qed (m, true)));
val global_terminal_proof = Toplevel.end_proof o K o Proof.global_future_terminal_proof;
val global_default_proof = Toplevel.end_proof (K Proof.global_default_proof);
val global_immediate_proof = Toplevel.end_proof (K Proof.global_immediate_proof);
val global_skip_proof = Toplevel.end_proof Proof.global_skip_proof;
val global_done_proof = Toplevel.end_proof (K Proof.global_done_proof);


(* common endings *)

fun qed m = local_qed m o global_qed m;
fun terminal_proof m = local_terminal_proof m o global_terminal_proof m;
val default_proof = local_default_proof o global_default_proof;
val immediate_proof = local_immediate_proof o global_immediate_proof;
val done_proof = local_done_proof o global_done_proof;
val skip_proof = local_skip_proof o global_skip_proof;


(* diagnostic ML evaluation *)

structure Diag_State = Proof_Data
(
  type T = Toplevel.state option;
  fun init _ = NONE;
);

fun ml_diag verbose source = Toplevel.keep (fn state =>
  let
    val opt_ctxt =
      try Toplevel.generic_theory_of state
      |> Option.map (Context.proof_of #> Diag_State.put (SOME state));
    val flags = ML_Compiler.verbose verbose ML_Compiler.flags;
  in ML_Context.eval_source_in opt_ctxt flags source end);

fun diag_state ctxt =
  (case Diag_State.get ctxt of
    SOME st => st
  | NONE => Toplevel.make_state NONE);

val diag_goal = Proof.goal o Toplevel.proof_of o diag_state;

val _ = Theory.setup
  (ML_Antiquotation.value (Binding.qualify true "Isar" \<^binding>\<open>state\<close>)
    (Scan.succeed "Isar_Cmd.diag_state ML_context") #>
   ML_Antiquotation.value (Binding.qualify true "Isar" \<^binding>\<open>goal\<close>)
    (Scan.succeed "Isar_Cmd.diag_goal ML_context"));


(* theorems of theory or proof context *)

fun pretty_theorems verbose st =
  if Toplevel.is_proof st then
    Proof_Context.pretty_local_facts verbose (Toplevel.context_of st)
  else
    let
      val ctxt = Toplevel.context_of st;
      val prev_thys =
        (case Toplevel.previous_theory_of st of
          SOME thy => [thy]
        | NONE => Theory.parents_of (Proof_Context.theory_of ctxt));
    in Proof_Display.pretty_theorems_diff verbose prev_thys ctxt end;


(* print theorems, terms, types etc. *)

local

fun pretty_stmts ctxt args =
  Attrib.eval_thms ctxt args
  |> map (Element.pretty_statement ctxt Thm.theoremK)
  |> Pretty.chunks2;

fun pretty_thms ctxt args =
  Proof_Context.pretty_fact ctxt ("", Attrib.eval_thms ctxt args);

fun pretty_prfs full state arg =
  (case arg of
    NONE =>
      let
        val {context = ctxt, goal = thm} = Proof.simple_goal (Toplevel.proof_of state);
        val thy = Proof_Context.theory_of ctxt;
        val prf = Thm.proof_of thm;
        val prop = Thm.full_prop_of thm;
        val prf' = Proofterm.rewrite_proof_notypes ([], []) prf;
      in
        Proof_Syntax.pretty_proof ctxt
          (if full then Proofterm.reconstruct_proof thy prop prf' else prf')
      end
  | SOME srcs =>
      let
        val ctxt = Toplevel.context_of state;
        val pretty_proof = Proof_Syntax.pretty_standard_proof_of ctxt full;
      in Pretty.chunks (map pretty_proof (Attrib.eval_thms ctxt srcs)) end);

fun pretty_prop ctxt s =
  let
    val prop = Syntax.read_prop ctxt s;
    val ctxt' = Proof_Context.augment prop ctxt;
  in Pretty.quote (Syntax.pretty_term ctxt' prop) end;

fun pretty_term ctxt s =
  let
    val t = Syntax.read_term ctxt s;
    val T = Term.type_of t;
    val ctxt' = Proof_Context.augment t ctxt;
  in
    Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t), Pretty.fbrk,
      Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' T)]
  end;

fun pretty_type ctxt (s, NONE) =
      let val T = Syntax.read_typ ctxt s
      in Pretty.quote (Syntax.pretty_typ ctxt T) end
  | pretty_type ctxt (s1, SOME s2) =
      let
        val ctxt' = Config.put show_sorts true ctxt;
        val raw_T = Syntax.parse_typ ctxt' s1;
        val S = Syntax.read_sort ctxt' s2;
        val T =
          Syntax.check_term ctxt'
            (Logic.mk_type raw_T |> Type.constraint (Term.itselfT (Type_Infer.anyT S)))
          |> Logic.dest_type;
      in Pretty.quote (Syntax.pretty_typ ctxt' T) end;

fun print_item pretty (modes, arg) = Toplevel.keep (fn state =>
  Print_Mode.with_modes modes (fn () => Pretty.writeln (pretty state arg)) ());

in

val print_stmts = print_item (pretty_stmts o Toplevel.context_of);
val print_thms = print_item (pretty_thms o Toplevel.context_of);
val print_prfs = print_item o pretty_prfs;
val print_prop = print_item (pretty_prop o Toplevel.context_of);
val print_term = print_item (pretty_term o Toplevel.context_of);
val print_type = print_item (pretty_type o Toplevel.context_of);

end;

end;
