(*  Title:      Pure/Isar/proof_context.ML
    Author:     Markus Wenzel, TU Muenchen

The key concept of Isar proof contexts: elevates primitive local
reasoning Gamma |- phi to a structured concept, with generic context
elements.  See also structure Variable and Assumption.
*)

signature PROOF_CONTEXT =
sig
  val theory_of: Proof.context -> theory
  val init_global: theory -> Proof.context
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
  val syntax_of: Proof.context -> Local_Syntax.T
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
  val map_naming: (Name_Space.naming -> Name_Space.naming) -> Proof.context -> Proof.context
  val naming_of: Proof.context -> Name_Space.naming
  val restore_naming: Proof.context -> Proof.context -> Proof.context
  val full_name: Proof.context -> binding -> string
  val class_space: Proof.context -> Name_Space.T
  val type_space: Proof.context -> Name_Space.T
  val const_space: Proof.context -> Name_Space.T
  val intern_class: Proof.context -> xstring -> string
  val intern_type: Proof.context -> xstring -> string
  val intern_const: Proof.context -> xstring -> string
  val extern_class: Proof.context -> string -> xstring
  val extern_type: Proof.context -> string -> xstring
  val extern_const: Proof.context -> string -> xstring
  val transfer_syntax: theory -> Proof.context -> Proof.context
  val transfer: theory -> Proof.context -> Proof.context
  val background_theory: (theory -> theory) -> Proof.context -> Proof.context
  val background_theory_result: (theory -> 'a * theory) -> Proof.context -> 'a * Proof.context
  val extern_fact: Proof.context -> string -> xstring
  val pretty_term_abbrev: Proof.context -> term -> Pretty.T
  val pretty_fact_aux: Proof.context -> bool -> string * thm list -> Pretty.T
  val pretty_fact: Proof.context -> string * thm list -> Pretty.T
  val read_class: Proof.context -> xstring -> class
  val read_typ: Proof.context -> string -> typ
  val read_typ_syntax: Proof.context -> string -> typ
  val read_typ_abbrev: Proof.context -> string -> typ
  val cert_typ: Proof.context -> typ -> typ
  val cert_typ_syntax: Proof.context -> typ -> typ
  val cert_typ_abbrev: Proof.context -> typ -> typ
  val infer_type: Proof.context -> string * typ -> typ
  val inferred_param: string -> Proof.context -> typ * Proof.context
  val inferred_fixes: Proof.context -> (string * typ) list * Proof.context
  val read_type_name: Proof.context -> bool -> string -> typ
  val read_type_name_proper: Proof.context -> bool -> string -> typ
  val read_const_proper: Proof.context -> bool -> string -> term
  val read_const: Proof.context -> bool -> typ -> string -> term
  val read_arity: Proof.context -> xstring * string list * string -> arity
  val cert_arity: Proof.context -> arity -> arity
  val allow_dummies: Proof.context -> Proof.context
  val prepare_sorts: Proof.context -> typ list -> typ list
  val check_tfree: Proof.context -> string * sort -> string * sort
  val intern_skolem: Proof.context -> string -> string option
  val read_term_pattern: Proof.context -> string -> term
  val read_term_schematic: Proof.context -> string -> term
  val read_term_abbrev: Proof.context -> string -> term
  val show_abbrevs_raw: Config.raw
  val show_abbrevs: bool Config.T
  val expand_abbrevs: Proof.context -> term -> term
  val cert_term: Proof.context -> term -> term
  val cert_prop: Proof.context -> term -> term
  val def_type: Proof.context -> indexname -> typ option
  val standard_typ_check: Proof.context -> typ list -> typ list
  val standard_term_check_finish: Proof.context -> term list -> term list
  val standard_term_uncheck: Proof.context -> term list -> term list
  val goal_export: Proof.context -> Proof.context -> thm list -> thm list
  val export: Proof.context -> Proof.context -> thm list -> thm list
  val export_morphism: Proof.context -> Proof.context -> morphism
  val norm_export_morphism: Proof.context -> Proof.context -> morphism
  val bind_terms: (indexname * term option) list -> Proof.context -> Proof.context
  val auto_bind_goal: term list -> Proof.context -> Proof.context
  val auto_bind_facts: term list -> Proof.context -> Proof.context
  val match_bind: bool -> (string list * string) list -> Proof.context -> term list * Proof.context
  val match_bind_i: bool -> (term list * term) list -> Proof.context -> term list * Proof.context
  val read_propp: (string * string list) list list -> Proof.context ->
    (term * term list) list list * Proof.context
  val cert_propp: (term * term list) list list -> Proof.context ->
    (term * term list) list list * Proof.context
  val read_propp_schematic: (string * string list) list list -> Proof.context ->
    (term * term list) list list * Proof.context
  val cert_propp_schematic: (term * term list) list list -> Proof.context ->
    (term * term list) list list * Proof.context
  val bind_propp: (string * string list) list list -> Proof.context ->
    (term list list * (Proof.context -> Proof.context)) * Proof.context
  val bind_propp_i: (term * term list) list list -> Proof.context ->
    (term list list * (Proof.context -> Proof.context)) * Proof.context
  val bind_propp_schematic: (string * string list) list list -> Proof.context ->
    (term list list * (Proof.context -> Proof.context)) * Proof.context
  val bind_propp_schematic_i: (term * term list) list list -> Proof.context ->
    (term list list * (Proof.context -> Proof.context)) * Proof.context
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
  val add_assms: Assumption.export ->
    (Thm.binding * (string * string list) list) list ->
    Proof.context -> (string * thm list) list * Proof.context
  val add_assms_i: Assumption.export ->
    (Thm.binding * (term * term list) list) list ->
    Proof.context -> (string * thm list) list * Proof.context
  val add_cases: bool -> (string * Rule_Cases.T option) list -> Proof.context -> Proof.context
  val apply_case: Rule_Cases.T -> Proof.context -> (string * term list) list * Proof.context
  val get_case: Proof.context -> string -> binding option list -> Rule_Cases.T
  val type_notation: bool -> Syntax.mode -> (typ * mixfix) list -> Proof.context -> Proof.context
  val notation: bool -> Syntax.mode -> (term * mixfix) list -> Proof.context -> Proof.context
  val generic_type_notation: bool -> Syntax.mode -> (typ * mixfix) list -> morphism ->
    Context.generic -> Context.generic
  val generic_notation: bool -> Syntax.mode -> (term * mixfix) list -> morphism ->
    Context.generic -> Context.generic
  val class_alias: binding -> class -> Proof.context -> Proof.context
  val type_alias: binding -> string -> Proof.context -> Proof.context
  val const_alias: binding -> string -> Proof.context -> Proof.context
  val add_const_constraint: string * typ option -> Proof.context -> Proof.context
  val add_abbrev: string -> binding * term -> Proof.context -> (term * term) * Proof.context
  val revert_abbrev: string -> string -> Proof.context -> Proof.context
  val generic_add_abbrev: string -> binding * term -> Context.generic ->
    (term * term) * Context.generic
  val generic_revert_abbrev: string -> string -> Context.generic -> Context.generic
  val print_syntax: Proof.context -> unit
  val print_abbrevs: Proof.context -> unit
  val print_binds: Proof.context -> unit
  val print_lthms: Proof.context -> unit
  val print_cases: Proof.context -> unit
  val debug: bool Config.T
  val verbose: bool Config.T
  val pretty_ctxt: Proof.context -> Pretty.T list
  val pretty_context: Proof.context -> Pretty.T list
end;

structure Proof_Context: PROOF_CONTEXT =
struct

val theory_of = Proof_Context.theory_of;
val init_global = Proof_Context.init_global;



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

datatype data =
  Data of
   {mode: mode,                  (*inner syntax mode*)
    syntax: Local_Syntax.T,      (*local syntax*)
    tsig: Type.tsig * Type.tsig, (*local/global type signature -- local name space / defsort only*)
    consts: Consts.T * Consts.T, (*local/global consts -- local name space / abbrevs only*)
    facts: Facts.T,              (*local facts*)
    cases: (string * (Rule_Cases.T * bool)) list};    (*named case contexts*)

fun make_data (mode, syntax, tsig, consts, facts, cases) =
  Data {mode = mode, syntax = syntax, tsig = tsig, consts = consts, facts = facts, cases = cases};

structure Data = Proof_Data
(
  type T = data;
  fun init thy =
    make_data (mode_default, Local_Syntax.init thy,
      (Sign.tsig_of thy, Sign.tsig_of thy),
      (Sign.consts_of thy, Sign.consts_of thy), Facts.empty, []);
);

fun rep_data ctxt = Data.get ctxt |> (fn Data rep => rep);

fun map_data f =
  Data.map (fn Data {mode, syntax, tsig, consts, facts, cases} =>
    make_data (f (mode, syntax, tsig, consts, facts, cases)));

fun set_mode mode = map_data (fn (_, syntax, tsig, consts, facts, cases) =>
  (mode, syntax, tsig, consts, facts, cases));

fun map_mode f =
  map_data (fn (Mode {stmt, pattern, schematic, abbrev}, syntax, tsig, consts, facts, cases) =>
    (make_mode (f (stmt, pattern, schematic, abbrev)), syntax, tsig, consts, facts, cases));

fun map_syntax f =
  map_data (fn (mode, syntax, tsig, consts, facts, cases) =>
    (mode, f syntax, tsig, consts, facts, cases));

fun map_tsig f =
  map_data (fn (mode, syntax, tsig, consts, facts, cases) =>
    (mode, syntax, f tsig, consts, facts, cases));

fun map_consts f =
  map_data (fn (mode, syntax, tsig, consts, facts, cases) =>
    (mode, syntax, tsig, f consts, facts, cases));

fun map_facts f =
  map_data (fn (mode, syntax, tsig, consts, facts, cases) =>
    (mode, syntax, tsig, consts, f facts, cases));

fun map_cases f =
  map_data (fn (mode, syntax, tsig, consts, facts, cases) =>
    (mode, syntax, tsig, consts, facts, f cases));

val get_mode = #mode o rep_data;
val restore_mode = set_mode o get_mode;
val abbrev_mode = get_mode #> (fn Mode {abbrev, ...} => abbrev);

fun set_stmt stmt =
  map_mode (fn (_, pattern, schematic, abbrev) => (stmt, pattern, schematic, abbrev));

val syntax_of = #syntax o rep_data;
val syn_of = Local_Syntax.syn_of o syntax_of;
val set_syntax_mode = map_syntax o Local_Syntax.set_mode;
val restore_syntax_mode = map_syntax o Local_Syntax.restore_mode o syntax_of;

val tsig_of = #1 o #tsig o rep_data;
val set_defsort = map_tsig o apfst o Type.set_defsort;
fun default_sort ctxt = the_default (Type.defaultS (tsig_of ctxt)) o Variable.def_sort ctxt;

val consts_of = #1 o #consts o rep_data;
val the_const_constraint = Consts.the_constraint o consts_of;

val facts_of = #facts o rep_data;
val cases_of = #cases o rep_data;


(* naming *)

val naming_of = Name_Space.naming_of o Context.Proof;
val map_naming = Context.proof_map o Name_Space.map_naming;
val restore_naming = map_naming o K o naming_of;

val full_name = Name_Space.full_name o naming_of;


(* name spaces *)

val class_space = Type.class_space o tsig_of;
val type_space = Type.type_space o tsig_of;
val const_space = Consts.space_of o consts_of;

val intern_class = Name_Space.intern o class_space;
val intern_type = Name_Space.intern o type_space;
val intern_const = Name_Space.intern o const_space;

fun extern_class ctxt = Name_Space.extern ctxt (class_space ctxt);
fun extern_type ctxt = Name_Space.extern ctxt (type_space ctxt);
fun extern_const ctxt = Name_Space.extern ctxt (const_space ctxt);


(* theory transfer *)

fun transfer_syntax thy ctxt = ctxt |>
  map_syntax (Local_Syntax.rebuild thy) |>
  map_tsig (fn tsig as (local_tsig, global_tsig) =>
    let val thy_tsig = Sign.tsig_of thy in
      if Type.eq_tsig (thy_tsig, global_tsig) then tsig
      else (Type.merge_tsig (Context.pretty ctxt) (local_tsig, thy_tsig), thy_tsig)
    end) |>
  map_consts (fn consts as (local_consts, global_consts) =>
    let val thy_consts = Sign.consts_of thy in
      if Consts.eq_consts (thy_consts, global_consts) then consts
      else (Consts.merge (local_consts, thy_consts), thy_consts)
    end);

fun transfer thy = Context.raw_transfer thy #> transfer_syntax thy;

fun background_theory f ctxt = transfer (f (theory_of ctxt)) ctxt;

fun background_theory_result f ctxt =
  let val (res, thy') = f (theory_of ctxt)
  in (res, ctxt |> transfer thy') end;



(** pretty printing **)

(* extern *)

fun which_facts ctxt name =
  let
    val local_facts = facts_of ctxt;
    val global_facts = Global_Theory.facts_of (theory_of ctxt);
  in
    if is_some (Facts.lookup (Context.Proof ctxt) local_facts name)
    then local_facts else global_facts
  end;

fun markup_fact ctxt name = Name_Space.markup (Facts.space_of (which_facts ctxt name)) name;

fun extern_fact ctxt name = Facts.extern ctxt (which_facts ctxt name) name;


(* pretty *)

fun pretty_term_abbrev ctxt = Syntax.pretty_term (set_mode mode_abbrev ctxt);

fun pretty_fact_name ctxt a =
  Pretty.block [Pretty.mark_str (markup_fact ctxt a, extern_fact ctxt a), Pretty.str ":"];

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
    val _ = Context_Position.report ctxt pos (Name_Space.markup (Type.class_space tsig) c);
  in c end;


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

(* check Skolem constants *)

fun no_skolem internal x =
  if can Name.dest_skolem x then
    error ("Illegal reference to internal Skolem constant: " ^ quote x)
  else if not internal andalso can Name.dest_internal x then
    error ("Illegal reference to internal variable: " ^ quote x)
  else x;



(** prepare terms and propositions **)

(* inferred types of parameters *)

fun infer_type ctxt x =
  Term.fastype_of (singleton (Syntax.check_terms (set_mode mode_schematic ctxt)) (Free x));

fun inferred_param x ctxt =
  let val T = infer_type ctxt (x, dummyT)
  in (T, ctxt |> Variable.declare_term (Free (x, T))) end;

fun inferred_fixes ctxt =
  let
    val xs = map #2 (Variable.dest_fixes ctxt);
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
      | NONE => Consts.read_const consts (c, pos));
    val _ =
      if strict then ignore (Consts.the_const consts d) handle TYPE (msg, _, _) => err msg
      else ();
    val _ = Context_Position.report ctxt pos (Name_Space.markup (Consts.space_of consts) d);
  in t end;

in

fun read_type_name ctxt strict text =
  let
    val tsig = tsig_of ctxt;
    val (c, pos) = token_content text;
  in
    if Lexicon.is_tid c then
     (Context_Position.report ctxt pos Isabelle_Markup.tfree;
      TFree (c, default_sort ctxt (c, ~1)))
    else
      let
        val d = intern_type ctxt c;
        val decl = Type.the_decl tsig (d, pos);
        fun err () = error ("Bad type name: " ^ quote d ^ Position.str_of pos);
        val args =
          (case decl of
            Type.LogicalType n => n
          | Type.Abbreviation (vs, _, _) => if strict then err () else length vs
          | Type.Nonterminal => if strict then err () else 0);
        val _ = Context_Position.report ctxt pos (Name_Space.markup (Type.type_space tsig) d);
      in Type (d, replicate args dummyT) end
  end;

fun read_type_name_proper ctxt strict text =
  (case read_type_name ctxt strict text of
    T as Type _ => T
  | T => error ("Not a type constructor: " ^ Syntax.string_of_typ ctxt T));


fun read_const_proper ctxt strict = prep_const_proper ctxt strict o token_content;

fun read_const ctxt strict ty text =
  let
    val (c, pos) = token_content text;
    val _ = no_skolem false c;
  in
    (case (Variable.lookup_fixed ctxt c, Variable.is_const ctxt c) of
      (SOME x, false) =>
        (Context_Position.report ctxt pos
            (Markup.name x
              (if can Name.dest_skolem x then Isabelle_Markup.skolem else Isabelle_Markup.free));
          Free (x, infer_type ctxt (x, ty)))
    | _ => prep_const_proper ctxt strict (c, pos))
  end;

end;


(* type arities *)

local

fun prep_arity prep_tycon prep_sort ctxt (t, Ss, S) =
  let val arity = (prep_tycon ctxt t, map (prep_sort ctxt) Ss, prep_sort ctxt S)
  in Type.add_arity (Context.pretty ctxt) arity (tsig_of ctxt); arity end;

in

val read_arity =
  prep_arity (fn ctxt => #1 o dest_Type o read_type_name_proper ctxt true) Syntax.read_sort;

val cert_arity = prep_arity (K I) (Type.cert_sort o tsig_of);

end;


(* skolem variables *)

fun intern_skolem ctxt x =
  let
    val _ = no_skolem false x;
    val sko = Variable.lookup_fixed ctxt x;
    val is_const = can (read_const_proper ctxt false) x orelse Long_Name.is_qualified x;
    val is_declared = is_some (Variable.def_type ctxt false (x, ~1));
  in
    if Variable.is_const ctxt x then NONE
    else if is_some sko then sko
    else if not is_const orelse is_declared then SOME x
    else NONE
  end;


(* read_term *)

fun read_term_mode mode ctxt = Syntax.read_term (set_mode mode ctxt);

val read_term_pattern   = read_term_mode mode_pattern;
val read_term_schematic = read_term_mode mode_schematic;
val read_term_abbrev    = read_term_mode mode_abbrev;


(* local abbreviations *)

local

fun certify_consts ctxt = Consts.certify (Context.pretty ctxt) (tsig_of ctxt)
  (not (abbrev_mode ctxt)) (consts_of ctxt);

fun expand_binds ctxt =
  let
    val Mode {pattern, schematic, ...} = get_mode ctxt;

    fun reject_schematic (t as Var _) =
          error ("Unbound schematic variable: " ^ Syntax.string_of_term ctxt t)
      | reject_schematic (Abs (_, _, t)) = reject_schematic t
      | reject_schematic (t $ u) = (reject_schematic t; reject_schematic u)
      | reject_schematic _ = ();
  in
    if pattern then I
    else Variable.expand_binds ctxt #> (if schematic then I else tap reject_schematic)
  end;

in

fun expand_abbrevs ctxt = certify_consts ctxt #> expand_binds ctxt;

end;

val show_abbrevs_raw = Config.declare "show_abbrevs" (fn _ => Config.Bool true);
val show_abbrevs = Config.bool show_abbrevs_raw;

fun contract_abbrevs ctxt t =
  let
    val thy = theory_of ctxt;
    val consts = consts_of ctxt;
    val Mode {abbrev, ...} = get_mode ctxt;
    val retrieve = Consts.retrieve_abbrevs consts (print_mode_value () @ [""]);
    fun match_abbrev u = Option.map #1 (get_first (Pattern.match_rew thy u) (retrieve u));
  in
    if abbrev orelse not (Config.get ctxt show_abbrevs) orelse not (can Term.type_of t) then t
    else Pattern.rewrite_term_top thy [] [match_abbrev] t
  end;


(* patterns *)

fun prepare_patternT ctxt T =
  let
    val Mode {pattern, schematic, ...} = get_mode ctxt;
    val _ =
      pattern orelse schematic orelse
        T |> Term.exists_subtype
          (fn T as TVar (xi, _) =>
            not (Type_Infer.is_param xi) andalso
              error ("Illegal schematic type variable: " ^ Syntax.string_of_typ ctxt T)
          | _ => false)
  in T end;


local

val dummies = Config.bool (Config.declare "Proof_Context.dummies" (K (Config.Bool false)));

fun check_dummies ctxt t =
  if Config.get ctxt dummies then t
  else Term.no_dummy_patterns t handle TERM _ => error "Illegal dummy pattern(s) in term";

fun prepare_dummies ts = #1 (fold_map Term.replace_dummy_patterns ts 1);

in

val allow_dummies = Config.put dummies true;

fun prepare_patterns ctxt =
  let val Mode {pattern, ...} = get_mode ctxt in
    Type_Infer.fixate ctxt #>
    pattern ? Variable.polymorphic ctxt #>
    (map o Term.map_types) (prepare_patternT ctxt) #>
    (if pattern then prepare_dummies else map (check_dummies ctxt))
  end;

end;


(* sort constraints *)

fun prepare_sorts ctxt tys =
  let
    val tsig = tsig_of ctxt;
    val defaultS = Type.defaultS tsig;

    fun constraint (xi, S) env =
      if S = dummyS then env
      else
        Vartab.insert (op =) (xi, Type.minimize_sort tsig S) env
          handle Vartab.DUP _ =>
            error ("Inconsistent sort constraints for type variable " ^
              quote (Term.string_of_vname' xi));
    val env =
      (fold o fold_atyps)
        (fn TFree (x, S) => constraint ((x, ~1), S)
          | TVar v => constraint v
          | _ => I) tys Vartab.empty;

    fun get_sort xi =
      (case (Vartab.lookup env xi, Variable.def_sort ctxt xi) of
        (NONE, NONE) => defaultS
      | (NONE, SOME S) => S
      | (SOME S, NONE) => S
      | (SOME S, SOME S') =>
          if Type.eq_sort tsig (S, S') then S'
          else
            error ("Sort constraint " ^ Syntax.string_of_sort ctxt S ^
              " inconsistent with default " ^ Syntax.string_of_sort ctxt S' ^
              " for type variable " ^ quote (Term.string_of_vname' xi)));
  in
    (map o map_atyps)
      (fn T =>
        if Term_Position.is_positionT T then T
        else
          (case T of
            TFree (x, _) => TFree (x, get_sort (x, ~1))
          | TVar (xi, _) => TVar (xi, get_sort xi)
          | _ => T)) tys
  end;

fun check_tfree ctxt v = dest_TFree (singleton (prepare_sorts ctxt) (TFree v));


(* certify terms *)

local

fun gen_cert prop ctxt t =
  t
  |> expand_abbrevs ctxt
  |> (fn t' =>
      #1 (Sign.certify' prop (Context.pretty ctxt) false (consts_of ctxt) (theory_of ctxt) t')
        handle TYPE (msg, _, _) => error msg | TERM (msg, _) => error msg);

in

val cert_term = gen_cert false;
val cert_prop = gen_cert true;

end;


(* check/uncheck *)

fun def_type ctxt =
  let val Mode {pattern, ...} = get_mode ctxt
  in Variable.def_type ctxt pattern end;

fun standard_typ_check ctxt =
  map (cert_typ_mode (Type.get_mode ctxt) ctxt #> prepare_patternT ctxt);

val standard_term_check_finish = prepare_patterns;

fun standard_term_uncheck ctxt = map (contract_abbrevs ctxt);



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
  map (Syntax.parse_term ctxt #> Type.constraint T) #> Syntax.check_terms ctxt;

val match_bind = gen_bind read_terms;
val match_bind_i = gen_bind (fn ctxt => fn _ => map (cert_term ctxt));

end;


(* propositions with patterns *)

local

fun prep_propp mode prep_props args context =
  let
    fun prep (_, raw_pats) (ctxt, prop :: props) =
      let val ctxt' = Variable.declare_term prop ctxt
      in ((prop, prep_props (set_mode mode_pattern ctxt') raw_pats), (ctxt', props)) end;

    val (propp, (context', _)) =
      (fold_map o fold_map) prep args
        (context, prep_props (set_mode mode context) (maps (map fst) args));
  in (propp, context') end;

fun gen_bind_propp mode parse_prop raw_args ctxt =
  let
    val (args, ctxt') = prep_propp mode parse_prop raw_args ctxt;
    val binds = flat (flat (map (map (simult_matches ctxt')) args));
    val propss = map (map #1) args;
    fun gen_binds ctxt0 = ctxt0
      |> bind_terms (map #1 binds ~~
          map (SOME o Term.close_schematic_term) (Variable.export_terms ctxt' ctxt0 (map #2 binds)));
  in ((propss, gen_binds), ctxt' |> bind_terms (map (apsnd SOME) binds)) end;

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
        val pos = Syntax.read_token_pos s;
        val prop =
          Syntax.read_prop (ctxt |> set_mode mode_default |> allow_dummies) s
          |> singleton (Variable.polymorphic ctxt);
        fun err msg = error (msg ^ Position.str_of pos ^ ":\n" ^ Syntax.string_of_term ctxt prop);

        val (prop', _) = Term.replace_dummy_patterns prop (Variable.maxidx_of ctxt + 1);
        fun prove_fact th =
          Goal.prove ctxt [] [] prop' (K (ALLGOALS (fact_tac [th])));
        val results = map_filter (try prove_fact) (potential_facts ctxt prop');
        val res =
          (case distinct Thm.eq_thm_prop results of
            [res] => res
          | [] => err "Failed to retrieve literal fact"
          | _ => err "Ambiguous specification of literal fact");
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
              SOME (_, ths) =>
                (Context_Position.report ctxt pos
                  (Name_Space.markup (Facts.space_of local_facts) name);
                 map (Thm.transfer thy) (Facts.select thmref ths))
            | NONE => Global_Theory.get_fact (Context.Proof ctxt) thy xthmref);
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
      (Facts.add_local (Context.Proof ctxt) do_props (b, ths) #> snd);

in

fun note_thmss kind = fold_map (fn ((b, more_atts), raw_facts) => fn ctxt =>
  let
    val name = full_name ctxt b;
    val facts = Global_Theory.name_thmss false name raw_facts;
    fun app (ths, atts) =
      fold_map (Thm.proof_attributes (surround (Thm.kind kind) (atts @ more_atts))) ths;
    val (res, ctxt') = fold_map app facts ctxt;
    val thms = Global_Theory.name_thms false false name (flat res);
    val Mode {stmt, ...} = get_mode ctxt;
  in ((name, thms), ctxt' |> update_thms stmt (b, SOME thms)) end);

fun put_thms do_props thms ctxt = ctxt
  |> map_naming (K Name_Space.local_naming)
  |> Context_Position.set_visible false
  |> update_thms do_props (apfst Binding.name thms)
  |> Context_Position.restore_visible ctxt
  |> restore_naming ctxt;

end;



(** basic logical entities **)

(* variables *)

fun declare_var (x, opt_T, mx) ctxt =
  let val T = (case opt_T of SOME T => T | NONE => Mixfix.mixfixT mx)
  in ((x, T, mx), ctxt |> Variable.declare_constraints (Free (x, T))) end;

local

fun prep_vars prep_typ internal =
  fold_map (fn (b, raw_T, mx) => fn ctxt =>
    let
      val x = Variable.check_name b;
      val _ = Lexicon.is_identifier (no_skolem internal x) orelse
        error ("Illegal variable name: " ^ Binding.print b);

      fun cond_tvars T =
        if internal then T
        else Type.no_tvars T handle TYPE (msg, _, _) => error msg;
      val opt_T = Option.map (cond_tvars o cert_typ ctxt o prep_typ ctxt) raw_T;
      val (_, ctxt') = ctxt |> declare_var (x, opt_T, mx);
    in ((b, opt_T, mx), ctxt') end);

in

val read_vars = prep_vars Syntax.read_typ false;
val cert_vars = prep_vars (K I) true;

end;


(* notation *)

local

fun type_syntax (Type (c, args), mx) =
      SOME (Local_Syntax.Type, (Lexicon.mark_type c, Mixfix.make_type (length args), mx))
  | type_syntax _ = NONE;

fun const_syntax _ (Free (x, T), mx) = SOME (Local_Syntax.Fixed, (x, T, mx))
  | const_syntax ctxt (Const (c, _), mx) =
      (case try (Consts.type_scheme (consts_of ctxt)) c of
        SOME T => SOME (Local_Syntax.Const, (Lexicon.mark_const c, T, mx))
      | NONE => NONE)
  | const_syntax _ _ = NONE;

fun gen_notation syntax add mode args ctxt =
  ctxt |> map_syntax
    (Local_Syntax.update_modesyntax (theory_of ctxt) add mode (map_filter (syntax ctxt) args));

in

val type_notation = gen_notation (K type_syntax);
val notation = gen_notation const_syntax;

fun generic_type_notation add mode args phi =
  let
    val args' = args |> map_filter (fn (T, mx) =>
      let
        val T' = Morphism.typ phi T;
        val similar = (case (T, T') of (Type (c, _), Type (c', _)) => c = c' | _ => false);
      in if similar then SOME (T', mx) else NONE end);
  in Context.mapping (Sign.type_notation add mode args') (type_notation add mode args') end;

fun generic_notation add mode args phi =
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
      handle ERROR msg => cat_error msg ("in constant abbreviation " ^ Binding.print b);
    val [t] = Variable.exportT_terms (Variable.declare_term t0 ctxt) ctxt [t0];
    val ((lhs, rhs), consts') = consts_of ctxt
      |> Consts.abbreviate (Context.Proof ctxt) (tsig_of ctxt) mode (b, t);
  in
    ctxt
    |> (map_consts o apfst) (K consts')
    |> Variable.declare_term rhs
    |> pair (lhs, rhs)
  end;

fun revert_abbrev mode c = (map_consts o apfst) (Consts.revert_abbrev mode c);

fun generic_add_abbrev mode arg =
  Context.mapping_result (Sign.add_abbrev mode arg) (add_abbrev mode arg);

fun generic_revert_abbrev mode arg =
  Context.mapping (Sign.revert_abbrev mode arg) (revert_abbrev mode arg);


(* fixes *)

fun add_fixes raw_vars ctxt =
  let
    val thy = theory_of ctxt;
    val vars = #1 (cert_vars raw_vars ctxt);
  in
    ctxt
    |> Variable.add_fixes_binding (map #1 vars)
    |-> (fn xs =>
      fold_map declare_var (map2 (fn x => fn (_, T, mx) => (x, T, mx)) xs vars)
      #-> (map_syntax o Local_Syntax.add_syntax thy o map (pair Local_Syntax.Fixed))
      #> pair xs)
  end;



(** assumptions **)

local

fun gen_assms prepp exp args ctxt =
  let
    val cert = Thm.cterm_of (theory_of ctxt);
    val ((propss, _), ctxt1) = prepp (map snd args) ctxt;
    val _ = Variable.warn_extra_tfrees ctxt ctxt1;
    val (premss, ctxt2) = fold_burrow (Assumption.add_assms exp o map cert) propss ctxt1;
  in
    ctxt2
    |> auto_bind_facts (flat propss)
    |> note_thmss "" (map fst args ~~ map (map (fn th => ([th], []))) premss)
  end;

in

val add_assms = gen_assms bind_propp;
val add_assms_i = gen_assms bind_propp_i;

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

fun fix (b, T) ctxt =
  let val ([x], ctxt') = add_fixes [(b, SOME T, NoSyn)] ctxt
  in (Free (x, T), ctxt') end;

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
      pairself (#constants o Consts.dest) (#consts (rep_data ctxt));
    fun add_abbr (_, (_, NONE)) = I
      | add_abbr (c, (T, SOME t)) =
          if not show_globals andalso Symtab.defined globals c then I
          else cons (c, Logic.mk_equals (Const (c, T), t));
    val abbrevs =
      Name_Space.extern_table ctxt (space, Symtab.make (Symtab.fold add_abbr consts []));
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
        prt_sect "fix" [] (Pretty.str o Binding.name_of o fst) fixes @
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

val debug = Config.bool (Config.declare "Proof_Context.debug" (K (Config.Bool false)));
val verbose = Config.bool (Config.declare "Proof_Context.verbose" (K (Config.Bool false)));

fun pretty_ctxt ctxt =
  if not (Config.get ctxt debug) then []
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
        filter_out ((can Name.dest_internal orf member (op =) structs) o #1)
          (Variable.dest_fixes ctxt);
      val prt_fixes =
        if null fixes then []
        else [Pretty.block (Pretty.str "fixed variables:" :: Pretty.brk 1 ::
          Pretty.commas (map prt_fix fixes))];

      (*prems*)
      val prems = Assumption.all_prems_of ctxt;
      val prt_prems =
        if null prems then []
        else [Pretty.big_list "prems:" (map (Display.pretty_thm ctxt) prems)];
    in prt_structs @ prt_fixes @ prt_prems end;


(* main context *)

fun pretty_context ctxt =
  let
    val verbose = Config.get ctxt verbose;
    fun verb f x = if verbose then f (x ()) else [];

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

val show_abbrevs = Proof_Context.show_abbrevs;

