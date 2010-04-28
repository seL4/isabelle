(*  Title:      Pure/Isar/proof_context.ML
    Author:     Markus Wenzel, TU Muenchen

The key concept of Isar proof contexts: elevates primitive local
reasoning Gamma |- phi to a structured concept, with generic context
elements.  See also structure Variable and Assumption.
*)

signature PROOF_CONTEXT =
sig
  val theory_of: Proof.context -> theory
  val init: theory -> Proof.context
  type mode
  val mode_default: mode
  val mode_stmt: mode
  val mode_pattern: mode
  val mode_schematic: mode
  val mode_abbrev: mode
  val set_mode: mode -> Proof.context -> Proof.context
  val get_mode: Proof.context -> mode
  val restore_mode: Proof.context -> Proof.context -> Proof.context
  val abbrev_mode: Proof.context -> bool
  val set_stmt: bool -> Proof.context -> Proof.context
  val local_naming: Name_Space.naming
  val map_naming: (Name_Space.naming -> Name_Space.naming) -> Proof.context -> Proof.context
  val naming_of: Proof.context -> Name_Space.naming
  val restore_naming: Proof.context -> Proof.context -> Proof.context
  val full_name: Proof.context -> binding -> string
  val syn_of: Proof.context -> Syntax.syntax
  val tsig_of: Proof.context -> Type.tsig
  val set_defsort: sort -> Proof.context -> Proof.context
  val default_sort: Proof.context -> indexname -> sort
  val consts_of: Proof.context -> Consts.T
  val the_const_constraint: Proof.context -> string -> typ
  val set_syntax_mode: Syntax.mode -> Proof.context -> Proof.context
  val restore_syntax_mode: Proof.context -> Proof.context -> Proof.context
  val facts_of: Proof.context -> Facts.T
  val cases_of: Proof.context -> (string * (Rule_Cases.T * bool)) list
  val transfer_syntax: theory -> Proof.context -> Proof.context
  val transfer: theory -> Proof.context -> Proof.context
  val theory: (theory -> theory) -> Proof.context -> Proof.context
  val theory_result: (theory -> 'a * theory) -> Proof.context -> 'a * Proof.context
  val extern_fact: Proof.context -> string -> xstring
  val pretty_term_abbrev: Proof.context -> term -> Pretty.T
  val pretty_fact_aux: Proof.context -> bool -> string * thm list -> Pretty.T
  val pretty_fact: Proof.context -> string * thm list -> Pretty.T
  val read_class: Proof.context -> xstring -> class
  val read_arity: Proof.context -> xstring * string list * string -> arity
  val cert_arity: Proof.context -> arity -> arity
  val read_typ: Proof.context -> string -> typ
  val read_typ_syntax: Proof.context -> string -> typ
  val read_typ_abbrev: Proof.context -> string -> typ
  val cert_typ: Proof.context -> typ -> typ
  val cert_typ_syntax: Proof.context -> typ -> typ
  val cert_typ_abbrev: Proof.context -> typ -> typ
  val get_skolem: Proof.context -> string -> string
  val revert_skolem: Proof.context -> string -> string
  val infer_type: Proof.context -> string -> typ
  val inferred_param: string -> Proof.context -> typ * Proof.context
  val inferred_fixes: Proof.context -> (string * typ) list * Proof.context
  val read_type_name: Proof.context -> bool -> string -> typ
  val read_type_name_proper: Proof.context -> bool -> string -> typ
  val read_const_proper: Proof.context -> bool -> string -> term
  val read_const: Proof.context -> bool -> string -> term
  val allow_dummies: Proof.context -> Proof.context
  val check_tvar: Proof.context -> indexname * sort -> indexname * sort
  val check_tfree: Proof.context -> string * sort -> string * sort
  val decode_term: Proof.context -> term -> term
  val standard_infer_types: Proof.context -> term list -> term list
  val read_term_pattern: Proof.context -> string -> term
  val read_term_schematic: Proof.context -> string -> term
  val read_term_abbrev: Proof.context -> string -> term
  val expand_abbrevs: Proof.context -> term -> term
  val cert_term: Proof.context -> term -> term
  val cert_prop: Proof.context -> term -> term
  val def_type: Proof.context -> indexname -> typ option
  val goal_export: Proof.context -> Proof.context -> thm list -> thm list
  val export: Proof.context -> Proof.context -> thm list -> thm list
  val export_morphism: Proof.context -> Proof.context -> morphism
  val norm_export_morphism: Proof.context -> Proof.context -> morphism
  val bind_terms: (indexname * term option) list -> Proof.context -> Proof.context
  val auto_bind_goal: term list -> Proof.context -> Proof.context
  val auto_bind_facts: term list -> Proof.context -> Proof.context
  val match_bind: bool -> (string list * string) list -> Proof.context -> term list * Proof.context
  val match_bind_i: bool -> (term list * term) list -> Proof.context -> term list * Proof.context
  val read_propp: Proof.context * (string * string list) list list
    -> Proof.context * (term * term list) list list
  val cert_propp: Proof.context * (term * term list) list list
    -> Proof.context * (term * term list) list list
  val read_propp_schematic: Proof.context * (string * string list) list list
    -> Proof.context * (term * term list) list list
  val cert_propp_schematic: Proof.context * (term * term list) list list
    -> Proof.context * (term * term list) list list
  val bind_propp: Proof.context * (string * string list) list list
    -> Proof.context * (term list list * (Proof.context -> Proof.context))
  val bind_propp_i: Proof.context * (term * term list) list list
    -> Proof.context * (term list list * (Proof.context -> Proof.context))
  val bind_propp_schematic: Proof.context * (string * string list) list list
    -> Proof.context * (term list list * (Proof.context -> Proof.context))
  val bind_propp_schematic_i: Proof.context * (term * term list) list list
    -> Proof.context * (term list list * (Proof.context -> Proof.context))
  val fact_tac: thm list -> int -> tactic
  val some_fact_tac: Proof.context -> int -> tactic
  val get_fact: Proof.context -> Facts.ref -> thm list
  val get_fact_single: Proof.context -> Facts.ref -> thm
  val get_thms: Proof.context -> xstring -> thm list
  val get_thm: Proof.context -> xstring -> thm
  val note_thmss: string -> (Thm.binding * (thm list * attribute list) list) list ->
    Proof.context -> (string * thm list) list * Proof.context
  val put_thms: bool -> string * thm list option -> Proof.context -> Proof.context
  val read_vars: (binding * string option * mixfix) list -> Proof.context ->
    (binding * typ option * mixfix) list * Proof.context
  val cert_vars: (binding * typ option * mixfix) list -> Proof.context ->
    (binding * typ option * mixfix) list * Proof.context
  val add_fixes: (binding * typ option * mixfix) list -> Proof.context ->
    string list * Proof.context
  val auto_fixes: Proof.context * (term list list * 'a) -> Proof.context * (term list list * 'a)
  val bind_fixes: string list -> Proof.context -> (term -> term) * Proof.context
  val add_assms: Assumption.export ->
    (Thm.binding * (string * string list) list) list ->
    Proof.context -> (string * thm list) list * Proof.context
  val add_assms_i: Assumption.export ->
    (Thm.binding * (term * term list) list) list ->
    Proof.context -> (string * thm list) list * Proof.context
  val add_cases: bool -> (string * Rule_Cases.T option) list -> Proof.context -> Proof.context
  val apply_case: Rule_Cases.T -> Proof.context -> (string * term list) list * Proof.context
  val get_case: Proof.context -> string -> string option list -> Rule_Cases.T
  val type_notation: bool -> Syntax.mode -> (typ * mixfix) list -> Proof.context -> Proof.context
  val notation: bool -> Syntax.mode -> (term * mixfix) list -> Proof.context -> Proof.context
  val target_type_notation: bool -> Syntax.mode -> (typ * mixfix) list -> morphism ->
    Context.generic -> Context.generic
  val target_notation: bool -> Syntax.mode -> (term * mixfix) list -> morphism ->
    Context.generic -> Context.generic
  val class_alias: binding -> class -> Proof.context -> Proof.context
  val type_alias: binding -> string -> Proof.context -> Proof.context
  val const_alias: binding -> string -> Proof.context -> Proof.context
  val add_const_constraint: string * typ option -> Proof.context -> Proof.context
  val add_abbrev: string -> binding * term -> Proof.context -> (term * term) * Proof.context
  val revert_abbrev: string -> string -> Proof.context -> Proof.context
  val print_syntax: Proof.context -> unit
  val print_abbrevs: Proof.context -> unit
  val print_binds: Proof.context -> unit
  val print_lthms: Proof.context -> unit
  val print_cases: Proof.context -> unit
  val debug: bool Unsynchronized.ref
  val verbose: bool Unsynchronized.ref
  val prems_limit: int Unsynchronized.ref
  val pretty_ctxt: Proof.context -> Pretty.T list
  val pretty_context: Proof.context -> Pretty.T list
end;

structure ProofContext: PROOF_CONTEXT =
struct

open ProofContext;


(** inner syntax mode **)

datatype mode =
  Mode of
   {stmt: bool,                (*inner statement mode*)
    pattern: bool,             (*pattern binding schematic variables*)
    schematic: bool,           (*term referencing loose schematic variables*)
    abbrev: bool};             (*abbrev mode -- no normalization*)

fun make_mode (stmt, pattern, schematic, abbrev) =
  Mode {stmt = stmt, pattern = pattern, schematic = schematic, abbrev = abbrev};

val mode_default   = make_mode (false, false, false, false);
val mode_stmt      = make_mode (true, false, false, false);
val mode_pattern   = make_mode (false, true, false, false);
val mode_schematic = make_mode (false, false, true, false);
val mode_abbrev    = make_mode (false, false, false, true);



(** Isar proof context information **)

datatype ctxt =
  Ctxt of
   {mode: mode,                  (*inner syntax mode*)
    naming: Name_Space.naming,   (*local naming conventions*)
    syntax: Local_Syntax.T,      (*local syntax*)
    tsig: Type.tsig * Type.tsig, (*local/global type signature -- local name space / defsort only*)
    consts: Consts.T * Consts.T, (*local/global consts -- local name space / abbrevs only*)
    facts: Facts.T,              (*local facts*)
    cases: (string * (Rule_Cases.T * bool)) list};    (*named case contexts*)

fun make_ctxt (mode, naming, syntax, tsig, consts, facts, cases) =
  Ctxt {mode = mode, naming = naming, syntax = syntax,
    tsig = tsig, consts = consts, facts = facts, cases = cases};

val local_naming = Name_Space.default_naming |> Name_Space.add_path "local";

structure ContextData = Proof_Data
(
  type T = ctxt;
  fun init thy =
    make_ctxt (mode_default, local_naming, Local_Syntax.init thy,
      (Sign.tsig_of thy, Sign.tsig_of thy),
      (Sign.consts_of thy, Sign.consts_of thy), Facts.empty, []);
);

fun rep_context ctxt = ContextData.get ctxt |> (fn Ctxt args => args);

fun map_context f =
  ContextData.map (fn Ctxt {mode, naming, syntax, tsig, consts, facts, cases} =>
    make_ctxt (f (mode, naming, syntax, tsig, consts, facts, cases)));

fun set_mode mode = map_context (fn (_, naming, syntax, tsig, consts, facts, cases) =>
  (mode, naming, syntax, tsig, consts, facts, cases));

fun map_mode f =
  map_context (fn (Mode {stmt, pattern, schematic, abbrev}, naming, syntax, tsig, consts, facts, cases) =>
    (make_mode (f (stmt, pattern, schematic, abbrev)), naming, syntax, tsig, consts, facts, cases));

fun map_naming f =
  map_context (fn (mode, naming, syntax, tsig, consts, facts, cases) =>
    (mode, f naming, syntax, tsig, consts, facts, cases));

fun map_syntax f =
  map_context (fn (mode, naming, syntax, tsig, consts, facts, cases) =>
    (mode, naming, f syntax, tsig, consts, facts, cases));

fun map_tsig f =
  map_context (fn (mode, naming, syntax, tsig, consts, facts, cases) =>
    (mode, naming, syntax, f tsig, consts, facts, cases));

fun map_consts f =
  map_context (fn (mode, naming, syntax, tsig, consts, facts, cases) =>
    (mode, naming, syntax, tsig, f consts, facts, cases));

fun map_facts f =
  map_context (fn (mode, naming, syntax, tsig, consts, facts, cases) =>
    (mode, naming, syntax, tsig, consts, f facts, cases));

fun map_cases f =
  map_context (fn (mode, naming, syntax, tsig, consts, facts, cases) =>
    (mode, naming, syntax, tsig, consts, facts, f cases));

val get_mode = #mode o rep_context;
val restore_mode = set_mode o get_mode;
val abbrev_mode = get_mode #> (fn Mode {abbrev, ...} => abbrev);

fun set_stmt stmt =
  map_mode (fn (_, pattern, schematic, abbrev) => (stmt, pattern, schematic, abbrev));

val naming_of = #naming o rep_context;
val restore_naming = map_naming o K o naming_of
val full_name = Name_Space.full_name o naming_of;

val syntax_of = #syntax o rep_context;
val syn_of = Local_Syntax.syn_of o syntax_of;
val set_syntax_mode = map_syntax o Local_Syntax.set_mode;
val restore_syntax_mode = map_syntax o Local_Syntax.restore_mode o syntax_of;

val tsig_of = #1 o #tsig o rep_context;
val set_defsort = map_tsig o apfst o Type.set_defsort;
fun default_sort ctxt = the_default (Type.defaultS (tsig_of ctxt)) o Variable.def_sort ctxt;

val consts_of = #1 o #consts o rep_context;
val the_const_constraint = Consts.the_constraint o consts_of;

val facts_of = #facts o rep_context;
val cases_of = #cases o rep_context;


(* theory transfer *)

fun transfer_syntax thy ctxt = ctxt |>
  map_syntax (Local_Syntax.rebuild thy) |>
  map_tsig (fn tsig as (local_tsig, global_tsig) =>
    let val thy_tsig = Sign.tsig_of thy in
      if Type.eq_tsig (thy_tsig, global_tsig) then tsig
      else (Type.merge_tsig (Syntax.pp ctxt) (local_tsig, thy_tsig), thy_tsig)
    end) |>
  map_consts (fn consts as (local_consts, global_consts) =>
    let val thy_consts = Sign.consts_of thy in
      if Consts.eq_consts (thy_consts, global_consts) then consts
      else (Consts.merge (local_consts, thy_consts), thy_consts)
    end);

fun transfer thy = Context.raw_transfer thy #> transfer_syntax thy;

fun theory f ctxt = transfer (f (theory_of ctxt)) ctxt;

fun theory_result f ctxt =
  let val (res, thy') = f (theory_of ctxt)
  in (res, ctxt |> transfer thy') end;



(** pretty printing **)

(* extern *)

fun extern_fact ctxt name =
  let
    val local_facts = facts_of ctxt;
    val global_facts = PureThy.facts_of (theory_of ctxt);
  in
    if is_some (Facts.lookup (Context.Proof ctxt) local_facts name)
    then Facts.extern local_facts name
    else Facts.extern global_facts name
  end;


(* pretty *)

fun pretty_term_abbrev ctxt = Syntax.pretty_term (set_mode mode_abbrev ctxt);

fun pretty_fact_name ctxt a = Pretty.block
  [Pretty.markup (Markup.fact a) [Pretty.str (extern_fact ctxt a)], Pretty.str ":"];

fun pretty_fact_aux ctxt flag ("", ths) =
      Display.pretty_thms_aux ctxt flag ths
  | pretty_fact_aux ctxt flag (a, [th]) = Pretty.block
      [pretty_fact_name ctxt a, Pretty.brk 1, Display.pretty_thm_aux ctxt flag th]
  | pretty_fact_aux ctxt flag (a, ths) = Pretty.block
      (Pretty.fbreaks (pretty_fact_name ctxt a :: map (Display.pretty_thm_aux ctxt flag) ths));

fun pretty_fact ctxt = pretty_fact_aux ctxt true;



(** prepare types **)

(* classes *)

fun read_class ctxt text =
  let
    val tsig = tsig_of ctxt;
    val (syms, pos) = Syntax.read_token text;
    val c = Type.cert_class tsig (Type.intern_class tsig (Symbol_Pos.content syms))
      handle TYPE (msg, _, _) => error (msg ^ Position.str_of pos);
    val _ = Position.report (Markup.tclass c) pos;
  in c end;


(* type arities *)

local

fun prep_arity prep_tycon prep_sort ctxt (t, Ss, S) =
  let val arity = (prep_tycon ctxt t, map (prep_sort ctxt) Ss, prep_sort ctxt S)
  in Type.add_arity (Syntax.pp ctxt) arity (tsig_of ctxt); arity end;

in

val read_arity = prep_arity (Type.intern_type o tsig_of) Syntax.read_sort;
val cert_arity = prep_arity (K I) (Type.cert_sort o tsig_of);

end;


(* types *)

fun read_typ_mode mode ctxt s =
  Syntax.read_typ (Type.set_mode mode ctxt) s;

val read_typ = read_typ_mode Type.mode_default;
val read_typ_syntax = read_typ_mode Type.mode_syntax;
val read_typ_abbrev = read_typ_mode Type.mode_abbrev;


fun cert_typ_mode mode ctxt T =
  Type.cert_typ_mode mode (tsig_of ctxt) T
    handle TYPE (msg, _, _) => error msg;

val cert_typ = cert_typ_mode Type.mode_default;
val cert_typ_syntax = cert_typ_mode Type.mode_syntax;
val cert_typ_abbrev = cert_typ_mode Type.mode_abbrev;



(** prepare variables **)

(* internalize Skolem constants *)

val lookup_skolem = AList.lookup (op =) o Variable.fixes_of;
fun get_skolem ctxt x = the_default x (lookup_skolem ctxt x);

fun no_skolem internal x =
  if can Name.dest_skolem x then
    error ("Illegal reference to internal Skolem constant: " ^ quote x)
  else if not internal andalso can Name.dest_internal x then
    error ("Illegal reference to internal variable: " ^ quote x)
  else x;


(* revert Skolem constants -- if possible *)

fun revert_skolem ctxt x =
  (case find_first (fn (_, y) => y = x) (Variable.fixes_of ctxt) of
    SOME (x', _) => if lookup_skolem ctxt x' = SOME x then x' else x
  | NONE => x);


(* default token translations *)

local

fun free_or_skolem ctxt x =
  (if can Name.dest_skolem x then Pretty.mark Markup.skolem (Pretty.str (revert_skolem ctxt x))
   else Pretty.mark Markup.free (Pretty.str x))
  |> Pretty.mark
    (if Variable.is_fixed ctxt x orelse Syntax.is_pretty_global ctxt then Markup.fixed x
     else Markup.hilite);

fun var_or_skolem _ s =
  (case Lexicon.read_variable s of
    SOME (x, i) =>
      (case try Name.dest_skolem x of
        NONE => Pretty.mark Markup.var (Pretty.str s)
      | SOME x' => Pretty.mark Markup.skolem
          (Pretty.str (setmp_CRITICAL show_question_marks true Term.string_of_vname (x', i))))
  | NONE => Pretty.mark Markup.var (Pretty.str s));

fun plain_markup m _ s = Pretty.mark m (Pretty.str s);

val token_trans =
 Syntax.tokentrans_mode ""
  [("tfree", plain_markup Markup.tfree),
   ("tvar", plain_markup Markup.tvar),
   ("free", free_or_skolem),
   ("bound", plain_markup Markup.bound),
   ("var", var_or_skolem),
   ("numeral", plain_markup Markup.numeral),
   ("inner_string", plain_markup Markup.inner_string)];

in val _ = Context.>> (Context.map_theory (Sign.add_tokentrfuns token_trans)) end;



(** prepare terms and propositions **)

(* inferred types of parameters *)

fun infer_type ctxt x =
  Term.fastype_of (singleton (Syntax.check_terms (set_mode mode_schematic ctxt))
    (Free (x, dummyT)));

fun inferred_param x ctxt =
  let val T = infer_type ctxt x
  in (T, ctxt |> Variable.declare_term (Free (x, T))) end;

fun inferred_fixes ctxt =
  let
    val xs = rev (map #2 (Variable.fixes_of ctxt));
    val (Ts, ctxt') = fold_map inferred_param xs ctxt;
  in (xs ~~ Ts, ctxt') end;


(* type and constant names *)

local

val token_content = Syntax.read_token #>> Symbol_Pos.content;

fun prep_const_proper ctxt strict (c, pos) =
  let
    fun err msg = error (msg ^ Position.str_of pos);
    val consts = consts_of ctxt;
    val t as Const (d, _) =
      (case Variable.lookup_const ctxt c of
        SOME d =>
          Const (d, Consts.type_scheme (consts_of ctxt) d handle TYPE (msg, _, _) => err msg)
      | NONE => Consts.read_const consts c);
    val _ =
      if strict then ignore (Consts.the_type consts d) handle TYPE (msg, _, _) => err msg
      else ();
    val _ = Position.report (Markup.const d) pos;
  in t end;

in

fun read_type_name ctxt strict text =
  let
    val tsig = tsig_of ctxt;
    val (c, pos) = token_content text;
  in
    if Syntax.is_tid c then
     (Position.report Markup.tfree pos;
      TFree (c, default_sort ctxt (c, ~1)))
    else
      let
        val d = Type.intern_type tsig c;
        val decl = Type.the_decl tsig d;
        val _ = Position.report (Markup.tycon d) pos;
        fun err () = error ("Bad type name: " ^ quote d);
        val args =
          (case decl of
            Type.LogicalType n => n
          | Type.Abbreviation (vs, _, _) => if strict then err () else length vs
          | Type.Nonterminal => if strict then err () else 0);
      in Type (d, replicate args dummyT) end
  end;

fun read_type_name_proper ctxt strict text =
  (case read_type_name ctxt strict text of
    T as Type _ => T
  | T => error ("Not a type constructor: " ^ Syntax.string_of_typ ctxt T));


fun read_const_proper ctxt strict = prep_const_proper ctxt strict o token_content;

fun read_const ctxt strict text =
  let val (c, pos) = token_content text in
    (case (lookup_skolem ctxt c, Variable.is_const ctxt c) of
      (SOME x, false) =>
        (Position.report (Markup.name x
            (if can Name.dest_skolem x then Markup.skolem else Markup.free)) pos;
          Free (x, infer_type ctxt x))
    | _ => prep_const_proper ctxt strict (c, pos))
  end;

end;


(* read_term *)

fun read_term_mode mode ctxt = Syntax.read_term (set_mode mode ctxt);

val read_term_pattern   = read_term_mode mode_pattern;
val read_term_schematic = read_term_mode mode_schematic;
val read_term_abbrev    = read_term_mode mode_abbrev;


(* local abbreviations *)

local

fun certify_consts ctxt = Consts.certify (Syntax.pp ctxt) (tsig_of ctxt)
  (not (abbrev_mode ctxt)) (consts_of ctxt);

fun reject_schematic (Var (xi, _)) =
      error ("Unbound schematic variable: " ^ Term.string_of_vname xi)
  | reject_schematic (Abs (_, _, t)) = reject_schematic t
  | reject_schematic (t $ u) = (reject_schematic t; reject_schematic u)
  | reject_schematic _ = ();

fun expand_binds ctxt =
  let val Mode {pattern, schematic, ...} = get_mode ctxt in
    if pattern then I
    else Variable.expand_binds ctxt #> (if schematic then I else tap reject_schematic)
  end;

in

fun expand_abbrevs ctxt = certify_consts ctxt #> expand_binds ctxt;

end;


fun contract_abbrevs ctxt t =
  let
    val thy = theory_of ctxt;
    val consts = consts_of ctxt;
    val Mode {abbrev, ...} = get_mode ctxt;
    val retrieve = Consts.retrieve_abbrevs consts (print_mode_value () @ [""]);
    fun match_abbrev u = Option.map #1 (get_first (Pattern.match_rew thy u) (retrieve u));
  in
    if abbrev orelse print_mode_active "no_abbrevs" orelse not (can Term.type_of t) then t
    else Pattern.rewrite_term_top thy [] [match_abbrev] t
  end;


(* patterns *)

fun prepare_patternT ctxt T =
  let
    val Mode {pattern, schematic, ...} = get_mode ctxt;
    val _ =
      pattern orelse schematic orelse
        T |> Term.exists_subtype
          (fn TVar (xi, _) =>
            not (TypeInfer.is_param xi) andalso
              error ("Illegal schematic type variable: " ^ Term.string_of_vname xi)
          | _ => false)
  in T end;


local

structure Allow_Dummies = Proof_Data(type T = bool fun init _ = false);

fun check_dummies ctxt t =
  if Allow_Dummies.get ctxt then t
  else Term.no_dummy_patterns t handle TERM _ => error "Illegal dummy pattern(s) in term";

fun prepare_dummies ts = #1 (fold_map Term.replace_dummy_patterns ts 1);

in

val allow_dummies = Allow_Dummies.put true;

fun prepare_patterns ctxt =
  let val Mode {pattern, ...} = get_mode ctxt in
    TypeInfer.fixate_params (Variable.names_of ctxt) #>
    pattern ? Variable.polymorphic ctxt #>
    (map o Term.map_types) (prepare_patternT ctxt) #>
    (if pattern then prepare_dummies else map (check_dummies ctxt))
  end;

end;


(* decoding raw terms (syntax trees) *)

(* types *)

fun get_sort ctxt raw_text =
  let
    val tsig = tsig_of ctxt;

    val text = distinct (op =) (map (apsnd (Type.minimize_sort tsig)) raw_text);
    val _ =
      (case duplicates (eq_fst (op =)) text of
        [] => ()
      | dups => error ("Inconsistent sort constraints for type variable(s) "
          ^ commas_quote (map (Term.string_of_vname' o fst) dups)));

    fun lookup xi =
      (case AList.lookup (op =) text xi of
        NONE => NONE
      | SOME S => if S = dummyS then NONE else SOME S);

    fun get xi =
      (case (lookup xi, Variable.def_sort ctxt xi) of
        (NONE, NONE) => Type.defaultS tsig
      | (NONE, SOME S) => S
      | (SOME S, NONE) => S
      | (SOME S, SOME S') =>
          if Type.eq_sort tsig (S, S') then S'
          else error ("Sort constraint " ^ Syntax.string_of_sort ctxt S ^
            " inconsistent with default " ^ Syntax.string_of_sort ctxt S' ^
            " for type variable " ^ quote (Term.string_of_vname' xi)));
  in get end;

fun check_tvar ctxt (xi, S) = (xi, get_sort ctxt [(xi, S)] xi);
fun check_tfree ctxt (x, S) = apfst fst (check_tvar ctxt ((x, ~1), S));

local

fun intern_skolem ctxt def_type x =
  let
    val _ = no_skolem false x;
    val sko = lookup_skolem ctxt x;
    val is_const = can (read_const_proper ctxt false) x orelse Long_Name.is_qualified x;
    val is_declared = is_some (def_type (x, ~1));
  in
    if Variable.is_const ctxt x then NONE
    else if is_some sko then sko
    else if not is_const orelse is_declared then SOME x
    else NONE
  end;

in

fun term_context ctxt =
  {get_sort = get_sort ctxt,
   map_const = fn a => ((true, #1 (Term.dest_Const (read_const_proper ctxt false a)))
     handle ERROR _ => (false, Consts.intern (consts_of ctxt) a)),
   map_free = intern_skolem ctxt (Variable.def_type ctxt false)};

fun decode_term ctxt =
  let val {get_sort, map_const, map_free} = term_context ctxt
  in Syntax.decode_term get_sort map_const map_free end;

end;


(* certify terms *)

local

fun gen_cert prop ctxt t =
  t
  |> expand_abbrevs ctxt
  |> (fn t' => #1 (Sign.certify' prop (Syntax.pp ctxt) false (consts_of ctxt) (theory_of ctxt) t')
    handle TYPE (msg, _, _) => error msg
      | TERM (msg, _) => error msg);

in

val cert_term = gen_cert false;
val cert_prop = gen_cert true;

end;


(* type checking/inference *)

fun def_type ctxt =
  let val Mode {pattern, ...} = get_mode ctxt
  in Variable.def_type ctxt pattern end;

fun standard_infer_types ctxt ts =
  TypeInfer.infer_types (Syntax.pp ctxt) (tsig_of ctxt) (Syntax.check_typs ctxt)
    (try (Consts.the_constraint (consts_of ctxt))) (def_type ctxt)
    (Variable.names_of ctxt) (Variable.maxidx_of ctxt) ts
  handle TYPE (msg, _, _) => error msg;

local

fun standard_typ_check ctxt =
  map (cert_typ_mode (Type.get_mode ctxt) ctxt) #>
  map (prepare_patternT ctxt);

fun standard_term_check ctxt =
  standard_infer_types ctxt #>
  map (expand_abbrevs ctxt);

fun standard_term_uncheck ctxt =
  map (contract_abbrevs ctxt);

fun add eq what f = Context.>> (what (fn xs => fn ctxt =>
  let val xs' = f ctxt xs in if eq_list eq (xs, xs') then NONE else SOME (xs', ctxt) end));

in

val _ = add (op =) (Syntax.add_typ_check 0 "standard") standard_typ_check;
val _ = add (op aconv) (Syntax.add_term_check 0 "standard") standard_term_check;
val _ = add (op aconv) (Syntax.add_term_check 100 "fixate") prepare_patterns;

val _ = add (op aconv) (Syntax.add_term_uncheck 0 "standard") standard_term_uncheck;

end;



(** inner syntax operations **)

local

fun parse_sort ctxt text =
  let
    val (syms, pos) = Syntax.parse_token Markup.sort text;
    val S = Syntax.standard_parse_sort ctxt (syn_of ctxt) (syms, pos)
      handle ERROR msg => cat_error msg  ("Failed to parse sort" ^ Position.str_of pos)
  in Type.minimize_sort (tsig_of ctxt) S end;

fun parse_typ ctxt text =
  let
    val (syms, pos) = Syntax.parse_token Markup.typ text;
    val T = Syntax.standard_parse_typ ctxt (syn_of ctxt) (get_sort ctxt) (syms, pos)
      handle ERROR msg => cat_error msg ("Failed to parse type" ^ Position.str_of pos);
  in T end;

fun parse_term T ctxt text =
  let
    val {get_sort, map_const, map_free} = term_context ctxt;

    val (T', _) = TypeInfer.paramify_dummies T 0;
    val (markup, kind) = if T' = propT then (Markup.prop, "proposition") else (Markup.term, "term");
    val (syms, pos) = Syntax.parse_token markup text;

    fun check t = (Syntax.check_term ctxt (TypeInfer.constrain T' t); NONE)
      handle ERROR msg => SOME msg;
    val t =
      Syntax.standard_parse_term (Syntax.pp ctxt) check get_sort map_const map_free
        ctxt (Type.is_logtype (tsig_of ctxt)) (syn_of ctxt) T' (syms, pos)
      handle ERROR msg => cat_error msg ("Failed to parse " ^ kind ^ Position.str_of pos);
  in t end;


fun unparse_sort ctxt =
  Syntax.standard_unparse_sort {extern_class = Type.extern_class (tsig_of ctxt)}
    ctxt (syn_of ctxt);

fun unparse_typ ctxt =
  let
    val tsig = tsig_of ctxt;
    val extern = {extern_class = Type.extern_class tsig, extern_type = Type.extern_type tsig};
  in Syntax.standard_unparse_typ extern ctxt (syn_of ctxt) end;

fun unparse_term ctxt =
  let
    val tsig = tsig_of ctxt;
    val syntax = syntax_of ctxt;
    val consts = consts_of ctxt;
    val extern =
     {extern_class = Type.extern_class tsig,
      extern_type = Type.extern_type tsig,
      extern_const = Consts.extern consts};
  in
    Syntax.standard_unparse_term (Local_Syntax.idents_of syntax) extern ctxt
      (Local_Syntax.syn_of syntax) (not (PureThy.old_appl_syntax (theory_of ctxt)))
  end;

in

val _ = Syntax.install_operations
  {parse_sort = parse_sort,
   parse_typ = parse_typ,
   parse_term = parse_term dummyT,
   parse_prop = parse_term propT,
   unparse_sort = unparse_sort,
   unparse_typ = unparse_typ,
   unparse_term = unparse_term};

end;



(** export results **)

fun common_export is_goal inner outer =
  map (Assumption.export is_goal inner outer) #>
  Variable.export inner outer;

val goal_export = common_export true;
val export = common_export false;

fun export_morphism inner outer =
  Assumption.export_morphism inner outer $>
  Variable.export_morphism inner outer;

fun norm_export_morphism inner outer =
  export_morphism inner outer $>
  Morphism.thm_morphism Goal.norm_result;



(** term bindings **)

(* simult_matches *)

fun simult_matches ctxt (t, pats) =
  (case Seq.pull (Unify.matchers (theory_of ctxt) (map (rpair t) pats)) of
    NONE => error "Pattern match failed!"
  | SOME (env, _) => Vartab.fold (fn (v, (_, t)) => cons (v, t)) (Envir.term_env env) []);


(* bind_terms *)

val bind_terms = fold (fn (xi, t) => fn ctxt =>
  ctxt
  |> Variable.bind_term (xi, Option.map (cert_term (set_mode mode_default ctxt)) t));


(* auto_bind *)

fun drop_schematic (b as (xi, SOME t)) = if Term.exists_subterm is_Var t then (xi, NONE) else b
  | drop_schematic b = b;

fun auto_bind f ts ctxt = ctxt |> bind_terms (map drop_schematic (f (theory_of ctxt) ts));

val auto_bind_goal = auto_bind Auto_Bind.goal;
val auto_bind_facts = auto_bind Auto_Bind.facts;


(* match_bind(_i) *)

local

fun gen_bind prep_terms gen raw_binds ctxt =
  let
    fun prep_bind (raw_pats, t) ctxt1 =
      let
        val T = Term.fastype_of t;
        val ctxt2 = Variable.declare_term t ctxt1;
        val pats = prep_terms (set_mode mode_pattern ctxt2) T raw_pats;
        val binds = simult_matches ctxt2 (t, pats);
      in (binds, ctxt2) end;

    val ts = prep_terms ctxt dummyT (map snd raw_binds);
    val (binds, ctxt') = apfst flat (fold_map prep_bind (map fst raw_binds ~~ ts) ctxt);
    val binds' =
      if gen then map #1 binds ~~ Variable.exportT_terms ctxt' ctxt (map #2 binds)
      else binds;
    val binds'' = map (apsnd SOME) binds';
    val ctxt'' =
      tap (Variable.warn_extra_tfrees ctxt)
       (if gen then
          ctxt (*sic!*) |> fold Variable.declare_term (map #2 binds') |> bind_terms binds''
        else ctxt' |> bind_terms binds'');
  in (ts, ctxt'') end;

in

fun read_terms ctxt T =
  map (Syntax.parse_term ctxt #> TypeInfer.constrain T) #> Syntax.check_terms ctxt;

val match_bind = gen_bind read_terms;
val match_bind_i = gen_bind (fn ctxt => fn _ => map (cert_term ctxt));

end;


(* propositions with patterns *)

local

fun prep_propp mode prep_props (context, args) =
  let
    fun prep (_, raw_pats) (ctxt, prop :: props) =
      let val ctxt' = Variable.declare_term prop ctxt
      in ((prop, prep_props (set_mode mode_pattern ctxt') raw_pats), (ctxt', props)) end;

    val (propp, (context', _)) = (fold_map o fold_map) prep args
      (context, prep_props (set_mode mode context) (maps (map fst) args));
  in (context', propp) end;

fun gen_bind_propp mode parse_prop (ctxt, raw_args) =
  let
    val (ctxt', args) = prep_propp mode parse_prop (ctxt, raw_args);
    val binds = flat (flat (map (map (simult_matches ctxt')) args));
    val propss = map (map #1) args;

    (*generalize result: context evaluated now, binds added later*)
    val gen = Variable.exportT_terms ctxt' ctxt;
    fun gen_binds c = c |> bind_terms (map #1 binds ~~ map SOME (gen (map #2 binds)));
  in (ctxt' |> bind_terms (map (apsnd SOME) binds), (propss, gen_binds)) end;

in

val read_propp           = prep_propp mode_default Syntax.read_props;
val cert_propp           = prep_propp mode_default (map o cert_prop);
val read_propp_schematic = prep_propp mode_schematic Syntax.read_props;
val cert_propp_schematic = prep_propp mode_schematic (map o cert_prop);

val bind_propp             = gen_bind_propp mode_default Syntax.read_props;
val bind_propp_i           = gen_bind_propp mode_default (map o cert_prop);
val bind_propp_schematic   = gen_bind_propp mode_schematic Syntax.read_props;
val bind_propp_schematic_i = gen_bind_propp mode_schematic (map o cert_prop);

end;



(** theorems **)

(* fact_tac *)

fun comp_incr_tac [] _ = no_tac
  | comp_incr_tac (th :: ths) i =
      (fn st => Goal.compose_hhf_tac (Drule.incr_indexes st th) i st) APPEND comp_incr_tac ths i;

fun fact_tac facts = Goal.norm_hhf_tac THEN' comp_incr_tac facts;

fun potential_facts ctxt prop =
  Facts.could_unify (facts_of ctxt) (Term.strip_all_body prop);

fun some_fact_tac ctxt = SUBGOAL (fn (goal, i) => fact_tac (potential_facts ctxt goal) i);


(* get_thm(s) *)

local

fun retrieve_thms pick ctxt (Facts.Fact s) =
      let
        val (_, pos) = Syntax.read_token s;
        val prop = Syntax.read_prop (set_mode mode_default ctxt) s
          |> singleton (Variable.polymorphic ctxt);

        fun prove_fact th =
          Goal.prove ctxt [] [] prop (K (ALLGOALS (fact_tac [th])));
        val res =
          (case get_first (try prove_fact) (potential_facts ctxt prop) of
            SOME res => res
          | NONE => error ("Failed to retrieve literal fact" ^ Position.str_of pos ^ ":\n" ^
              Syntax.string_of_term ctxt prop))
      in pick "" [res] end
  | retrieve_thms pick ctxt xthmref =
      let
        val thy = theory_of ctxt;
        val local_facts = facts_of ctxt;
        val thmref = Facts.map_name_of_ref (Facts.intern local_facts) xthmref;
        val name = Facts.name_of_ref thmref;
        val pos = Facts.pos_of_ref xthmref;
        val thms =
          if name = "" then [Thm.transfer thy Drule.dummy_thm]
          else
            (case Facts.lookup (Context.Proof ctxt) local_facts name of
              SOME (_, ths) => (Position.report (Markup.local_fact name) pos;
                map (Thm.transfer thy) (Facts.select thmref ths))
            | NONE => PureThy.get_fact (Context.Proof ctxt) thy xthmref);
      in pick name thms end;

in

val get_fact = retrieve_thms (K I);
val get_fact_single = retrieve_thms Facts.the_single;

fun get_thms ctxt = get_fact ctxt o Facts.named;
fun get_thm ctxt = get_fact_single ctxt o Facts.named;

end;


(* facts *)

local

fun update_thms _ (b, NONE) ctxt = ctxt |> map_facts (Facts.del (full_name ctxt b))
  | update_thms do_props (b, SOME ths) ctxt = ctxt |> map_facts
      (Facts.add_local do_props (naming_of ctxt) (b, ths) #> snd);

in

fun note_thmss kind = fold_map (fn ((b, more_attrs), raw_facts) => fn ctxt =>
  let
    val pos = Binding.pos_of b;
    val name = full_name ctxt b;
    val _ = Context_Position.report_visible ctxt (Markup.local_fact_decl name) pos;

    val facts = PureThy.name_thmss false name raw_facts;
    fun app (th, attrs) x =
      swap (Library.foldl_map
        (Thm.proof_attributes (surround (Thm.kind kind) (attrs @ more_attrs))) (x, th));
    val (res, ctxt') = fold_map app facts ctxt;
    val thms = PureThy.name_thms false false name (flat res);
    val Mode {stmt, ...} = get_mode ctxt;
  in ((name, thms), ctxt' |> update_thms stmt (b, SOME thms)) end);

fun put_thms do_props thms ctxt = ctxt
  |> map_naming (K local_naming)
  |> Context_Position.set_visible false
  |> update_thms do_props (apfst Binding.name thms)
  |> Context_Position.restore_visible ctxt
  |> restore_naming ctxt;

end;



(** basic logical entities **)

(* variables *)

fun declare_var (x, opt_T, mx) ctxt =
  let val T = (case opt_T of SOME T => T | NONE => Syntax.mixfixT mx)
  in ((x, T, mx), ctxt |> Variable.declare_constraints (Free (x, T))) end;

local

fun prep_vars prep_typ internal =
  fold_map (fn (b, raw_T, mx) => fn ctxt =>
    let
      val x = Name.of_binding b;
      val _ = Syntax.is_identifier (no_skolem internal x) orelse
        error ("Illegal variable name: " ^ quote (Binding.str_of b));

      fun cond_tvars T =
        if internal then T
        else Type.no_tvars T handle TYPE (msg, _, _) => error msg;
      val opt_T = Option.map (cond_tvars o cert_typ ctxt o prep_typ ctxt) raw_T;
      val (_, ctxt') = ctxt |> declare_var (x, opt_T, mx);
    in ((b, opt_T, mx), ctxt') end);

in

val read_vars = prep_vars Syntax.parse_typ false;
val cert_vars = prep_vars (K I) true;

end;


(* authentic syntax *)

val _ = Context.>>
  (Context.map_theory
    (Sign.add_advanced_trfuns
      (Syntax.type_ast_trs
        {read_class = read_class,
          read_type = fn ctxt => #1 o dest_Type o read_type_name_proper ctxt false}, [], [], [])));

local

fun const_ast_tr intern ctxt [Syntax.Variable c] =
      let
        val Const (c', _) = read_const_proper ctxt false c;
        val d = if intern then Syntax.mark_const c' else c;
      in Syntax.Constant d end
  | const_ast_tr _ _ asts = raise Syntax.AST ("const_ast_tr", asts);

val typ = Simple_Syntax.read_typ;

in

val _ = Context.>> (Context.map_theory
 (Sign.add_syntax_i
   [("_context_const", typ "id => logic", Delimfix "CONST _"),
    ("_context_const", typ "id => aprop", Delimfix "CONST _"),
    ("_context_const", typ "longid => logic", Delimfix "CONST _"),
    ("_context_const", typ "longid => aprop", Delimfix "CONST _"),
    ("_context_xconst", typ "id => logic", Delimfix "XCONST _"),
    ("_context_xconst", typ "id => aprop", Delimfix "XCONST _"),
    ("_context_xconst", typ "longid => logic", Delimfix "XCONST _"),
    ("_context_xconst", typ "longid => aprop", Delimfix "XCONST _")] #>
  Sign.add_advanced_trfuns
    ([("_context_const", const_ast_tr true), ("_context_xconst", const_ast_tr false)], [], [], [])));

end;


(* notation *)

local

fun type_syntax (Type (c, args), mx) =
      SOME (Local_Syntax.Type, (Syntax.mark_type c, Syntax.make_type (length args), mx))
  | type_syntax _ = NONE;

fun const_syntax _ (Free (x, T), mx) = SOME (Local_Syntax.Fixed, (x, T, mx))
  | const_syntax ctxt (Const (c, _), mx) =
      (case try (Consts.type_scheme (consts_of ctxt)) c of
        SOME T => SOME (Local_Syntax.Const, (Syntax.mark_const c, T, mx))
      | NONE => NONE)
  | const_syntax _ _ = NONE;

fun gen_notation syntax add mode args ctxt =
  ctxt |> map_syntax
    (Local_Syntax.update_modesyntax (theory_of ctxt) add mode (map_filter (syntax ctxt) args));

in

val type_notation = gen_notation (K type_syntax);
val notation = gen_notation const_syntax;

fun target_type_notation add  mode args phi =
  let
    val args' = args |> map_filter (fn (T, mx) =>
      let
        val T' = Morphism.typ phi T;
        val similar = (case (T, T') of (Type (c, _), Type (c', _)) => c = c' | _ => false);
      in if similar then SOME (T', mx) else NONE end);
  in Context.mapping (Sign.type_notation add mode args') (type_notation add mode args') end;

fun target_notation add mode args phi =
  let
    val args' = args |> map_filter (fn (t, mx) =>
      let val t' = Morphism.term phi t
      in if Term.aconv_untyped (t, t') then SOME (t', mx) else NONE end);
  in Context.mapping (Sign.notation add mode args') (notation add mode args') end;

end;


(* aliases *)

fun class_alias b c ctxt = (map_tsig o apfst) (Type.class_alias (naming_of ctxt) b c) ctxt;
fun type_alias b c ctxt = (map_tsig o apfst) (Type.type_alias (naming_of ctxt) b c) ctxt;
fun const_alias b c ctxt = (map_consts o apfst) (Consts.alias (naming_of ctxt) b c) ctxt;


(* local constants *)

fun add_const_constraint (c, opt_T) ctxt =
  let
    fun prepT raw_T =
      let val T = cert_typ ctxt raw_T
      in cert_term ctxt (Const (c, T)); T end;
  in ctxt |> (map_consts o apfst) (Consts.constrain (c, Option.map prepT opt_T)) end;

fun add_abbrev mode (b, raw_t) ctxt =
  let
    val t0 = cert_term (ctxt |> set_mode mode_abbrev) raw_t
      handle ERROR msg => cat_error msg ("in constant abbreviation " ^ quote (Binding.str_of b));
    val [t] = Variable.exportT_terms (Variable.declare_term t0 ctxt) ctxt [t0];
    val ((lhs, rhs), consts') = consts_of ctxt
      |> Consts.abbreviate (Syntax.pp ctxt) (tsig_of ctxt) (naming_of ctxt) mode (b, t);
  in
    ctxt
    |> (map_consts o apfst) (K consts')
    |> Variable.declare_term rhs
    |> pair (lhs, rhs)
  end;

fun revert_abbrev mode c = (map_consts o apfst) (Consts.revert_abbrev mode c);


(* fixes *)

local

fun prep_mixfix (x, T, mx) =
  if mx <> NoSyn andalso mx <> Structure andalso
      (can Name.dest_internal x orelse can Name.dest_skolem x) then
    error ("Illegal mixfix syntax for internal/skolem constant " ^ quote x)
  else (Local_Syntax.Fixed, (x, T, mx));

in

fun add_fixes raw_vars ctxt =
  let
    val (vars, _) = cert_vars raw_vars ctxt;
    val (xs', ctxt') = Variable.add_fixes (map (Name.of_binding o #1) vars) ctxt;
    val ctxt'' =
      ctxt'
      |> fold_map declare_var (map2 (fn x' => fn (_, T, mx) => (x', T, mx)) xs' vars)
      |-> (map_syntax o Local_Syntax.add_syntax (theory_of ctxt) o map prep_mixfix);
    val _ = (vars ~~ xs') |> List.app (fn ((b, _, _), x') =>
      Context_Position.report_visible ctxt (Markup.fixed_decl x') (Binding.pos_of b));
  in (xs', ctxt'') end;

end;


(* fixes vs. frees *)

fun auto_fixes (ctxt, (propss, x)) =
  ((fold o fold) Variable.auto_fixes propss ctxt, (propss, x));

fun bind_fixes xs ctxt =
  let
    val (_, ctxt') = ctxt |> add_fixes (map (fn x => (Binding.name x, NONE, NoSyn)) xs);
    fun bind (t as Free (x, T)) =
          if member (op =) xs x then
            (case lookup_skolem ctxt' x of SOME x' => Free (x', T) | NONE => t)
          else t
      | bind (t $ u) = bind t $ bind u
      | bind (Abs (x, T, t)) = Abs (x, T, bind t)
      | bind a = a;
  in (bind, ctxt') end;



(** assumptions **)

local

fun gen_assms prepp exp args ctxt =
  let
    val cert = Thm.cterm_of (theory_of ctxt);
    val (propss, ctxt1) = swap (prepp (ctxt, map snd args));
    val _ = Variable.warn_extra_tfrees ctxt ctxt1;
    val (premss, ctxt2) = fold_burrow (Assumption.add_assms exp o map cert) propss ctxt1;
  in
    ctxt2
    |> auto_bind_facts (flat propss)
    |> note_thmss "" (map fst args ~~ map (map (fn th => ([th], []))) premss)
  end;

in

val add_assms = gen_assms (apsnd #1 o bind_propp);
val add_assms_i = gen_assms (apsnd #1 o bind_propp_i);

end;



(** cases **)

local

fun rem_case name = remove (fn (x: string, (y, _)) => x = y) name;

fun add_case _ ("", _) cases = cases
  | add_case _ (name, NONE) cases = rem_case name cases
  | add_case is_proper (name, SOME c) cases = (name, (c, is_proper)) :: rem_case name cases;

fun prep_case name fxs c =
  let
    fun replace (opt_x :: xs) ((y, T) :: ys) = (the_default y opt_x, T) :: replace xs ys
      | replace [] ys = ys
      | replace (_ :: _) [] = error ("Too many parameters for case " ^ quote name);
    val Rule_Cases.Case {fixes, assumes, binds, cases} = c;
    val fixes' = replace fxs fixes;
    val binds' = map drop_schematic binds;
  in
    if null (fold (Term.add_tvarsT o snd) fixes []) andalso
      null (fold (fold Term.add_vars o snd) assumes []) then
        Rule_Cases.Case {fixes = fixes', assumes = assumes, binds = binds', cases = cases}
    else error ("Illegal schematic variable(s) in case " ^ quote name)
  end;

fun fix (x, T) ctxt =
  let
    val (bind, ctxt') = bind_fixes [x] ctxt;
    val t = bind (Free (x, T));
  in (t, ctxt' |> Variable.declare_constraints t) end;

in

fun add_cases is_proper = map_cases o fold (add_case is_proper);

fun case_result c ctxt =
  let
    val Rule_Cases.Case {fixes, ...} = c;
    val (ts, ctxt') = ctxt |> fold_map fix fixes;
    val Rule_Cases.Case {assumes, binds, cases, ...} = Rule_Cases.apply ts c;
  in
    ctxt'
    |> bind_terms (map drop_schematic binds)
    |> add_cases true (map (apsnd SOME) cases)
    |> pair (assumes, (binds, cases))
  end;

val apply_case = apfst fst oo case_result;

fun get_case ctxt name xs =
  (case AList.lookup (op =) (cases_of ctxt) name of
    NONE => error ("Unknown case: " ^ quote name)
  | SOME (c, _) => prep_case name xs c);

end;



(** print context information **)

(* local syntax *)

val print_syntax = Syntax.print_syntax o syn_of;


(* abbreviations *)

fun pretty_abbrevs show_globals ctxt =
  let
    val ((space, consts), (_, globals)) =
      pairself (#constants o Consts.dest) (#consts (rep_context ctxt));
    fun add_abbr (_, (_, NONE)) = I
      | add_abbr (c, (T, SOME t)) =
          if not show_globals andalso Symtab.defined globals c then I
          else cons (c, Logic.mk_equals (Const (c, T), t));
    val abbrevs = Name_Space.extern_table (space, Symtab.make (Symtab.fold add_abbr consts []));
  in
    if null abbrevs then []
    else [Pretty.big_list "abbreviations:" (map (pretty_term_abbrev ctxt o #2) abbrevs)]
  end;

val print_abbrevs = Pretty.writeln o Pretty.chunks o pretty_abbrevs true;


(* term bindings *)

fun pretty_binds ctxt =
  let
    val binds = Variable.binds_of ctxt;
    fun prt_bind (xi, (T, t)) = pretty_term_abbrev ctxt (Logic.mk_equals (Var (xi, T), t));
  in
    if Vartab.is_empty binds then []
    else [Pretty.big_list "term bindings:" (map prt_bind (Vartab.dest binds))]
  end;

val print_binds = Pretty.writeln o Pretty.chunks o pretty_binds;


(* local theorems *)

fun pretty_lthms ctxt =
  let
    val local_facts = facts_of ctxt;
    val props = Facts.props local_facts;
    val facts =
      (if null props then [] else [("<unnamed>", props)]) @
      Facts.dest_static [] local_facts;
  in
    if null facts then []
    else [Pretty.big_list "facts:" (map #1 (sort_wrt (#1 o #2) (map (`(pretty_fact ctxt)) facts)))]
  end;

val print_lthms = Pretty.writeln o Pretty.chunks o pretty_lthms;


(* local contexts *)

local

fun pretty_case (name, (fixes, ((asms, (lets, cs)), ctxt))) =
  let
    val prt_term = Syntax.pretty_term ctxt;

    fun prt_let (xi, t) = Pretty.block
      [Pretty.quote (prt_term (Var (xi, Term.fastype_of t))), Pretty.str " =", Pretty.brk 1,
        Pretty.quote (prt_term t)];

    fun prt_asm (a, ts) = Pretty.block (Pretty.breaks
      ((if a = "" then [] else [Pretty.str (a ^ ":")]) @ map (Pretty.quote o prt_term) ts));

    fun prt_sect _ _ _ [] = []
      | prt_sect s sep prt xs =
          [Pretty.block (Pretty.breaks (Pretty.str s ::
            flat (separate sep (map (single o prt) xs))))];
  in
    Pretty.block (Pretty.fbreaks
      (Pretty.str (name ^ ":") ::
        prt_sect "fix" [] (Pretty.str o fst) fixes @
        prt_sect "let" [Pretty.str "and"] prt_let
          (map_filter (fn (xi, SOME t) => SOME (xi, t) | _ => NONE) lets) @
        (if forall (null o #2) asms then []
          else prt_sect "assume" [Pretty.str "and"] prt_asm asms) @
        prt_sect "subcases:" [] (Pretty.str o fst) cs))
  end;

in

fun pretty_cases ctxt =
  let
    fun add_case (_, (_, false)) = I
      | add_case (name, (c as Rule_Cases.Case {fixes, ...}, true)) =
          cons (name, (fixes, case_result c ctxt));
    val cases = fold add_case (cases_of ctxt) [];
  in
    if null cases then []
    else [Pretty.big_list "cases:" (map pretty_case cases)]
  end;

val print_cases = Pretty.writeln o Pretty.chunks o pretty_cases;

end;


(* core context *)

val debug = Unsynchronized.ref false;
val verbose = Unsynchronized.ref false;
val prems_limit = Unsynchronized.ref ~1;

fun pretty_ctxt ctxt =
  if ! prems_limit < 0 andalso not (! debug) then []
  else
    let
      val prt_term = Syntax.pretty_term ctxt;

      (*structures*)
      val {structs, ...} = Local_Syntax.idents_of (syntax_of ctxt);
      val prt_structs =
        if null structs then []
        else [Pretty.block (Pretty.str "structures:" :: Pretty.brk 1 ::
          Pretty.commas (map Pretty.str structs))];

      (*fixes*)
      fun prt_fix (x, x') =
        if x = x' then Pretty.str x
        else Pretty.block [Pretty.str x, Pretty.str " =", Pretty.brk 1, prt_term (Syntax.free x')];
      val fixes =
        rev (filter_out ((can Name.dest_internal orf member (op =) structs) o #1)
          (Variable.fixes_of ctxt));
      val prt_fixes =
        if null fixes then []
        else [Pretty.block (Pretty.str "fixed variables:" :: Pretty.brk 1 ::
          Pretty.commas (map prt_fix fixes))];

      (*prems*)
      val prems = Assumption.all_prems_of ctxt;
      val len = length prems;
      val suppressed = len - ! prems_limit;
      val prt_prems =
        if null prems then []
        else [Pretty.big_list "prems:" ((if suppressed <= 0 then [] else [Pretty.str "..."]) @
          map (Display.pretty_thm ctxt) (drop suppressed prems))];
    in prt_structs @ prt_fixes @ prt_prems end;


(* main context *)

fun pretty_context ctxt =
  let
    val is_verbose = ! verbose;
    fun verb f x = if is_verbose then f (x ()) else [];

    val prt_term = Syntax.pretty_term ctxt;
    val prt_typ = Syntax.pretty_typ ctxt;
    val prt_sort = Syntax.pretty_sort ctxt;

    (*theory*)
    val pretty_thy = Pretty.block
      [Pretty.str "theory:", Pretty.brk 1, Context.pretty_thy (theory_of ctxt)];

    (*defaults*)
    fun prt_atom prt prtT (x, X) = Pretty.block
      [prt x, Pretty.str " ::", Pretty.brk 1, prtT X];

    fun prt_var (x, ~1) = prt_term (Syntax.free x)
      | prt_var xi = prt_term (Syntax.var xi);

    fun prt_varT (x, ~1) = prt_typ (TFree (x, []))
      | prt_varT xi = prt_typ (TVar (xi, []));

    val prt_defT = prt_atom prt_var prt_typ;
    val prt_defS = prt_atom prt_varT prt_sort;

    val (types, sorts) = Variable.constraints_of ctxt;
  in
    verb single (K pretty_thy) @
    pretty_ctxt ctxt @
    verb (pretty_abbrevs false) (K ctxt) @
    verb pretty_binds (K ctxt) @
    verb pretty_lthms (K ctxt) @
    verb pretty_cases (K ctxt) @
    verb single (fn () => Pretty.big_list "type constraints:" (map prt_defT (Vartab.dest types))) @
    verb single (fn () => Pretty.big_list "default sorts:" (map prt_defS (Vartab.dest sorts)))
  end;

end;

