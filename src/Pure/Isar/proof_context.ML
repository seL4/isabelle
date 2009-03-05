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
  val naming_of: Proof.context -> NameSpace.naming
  val full_name: Proof.context -> binding -> string
  val consts_of: Proof.context -> Consts.T
  val const_syntax_name: Proof.context -> string -> string
  val the_const_constraint: Proof.context -> string -> typ
  val mk_const: Proof.context -> string * typ list -> term
  val set_syntax_mode: Syntax.mode -> Proof.context -> Proof.context
  val restore_syntax_mode: Proof.context -> Proof.context -> Proof.context
  val facts_of: Proof.context -> Facts.T
  val transfer_syntax: theory -> Proof.context -> Proof.context
  val transfer: theory -> Proof.context -> Proof.context
  val theory: (theory -> theory) -> Proof.context -> Proof.context
  val theory_result: (theory -> 'a * theory) -> Proof.context -> 'a * Proof.context
  val extern_fact: Proof.context -> string -> xstring
  val pretty_term_abbrev: Proof.context -> term -> Pretty.T
  val pretty_thm_legacy: thm -> Pretty.T
  val pretty_thm: Proof.context -> thm -> Pretty.T
  val pretty_thms: Proof.context -> thm list -> Pretty.T
  val pretty_fact: Proof.context -> string * thm list -> Pretty.T
  val string_of_thm: Proof.context -> thm -> string
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
  val read_tyname: Proof.context -> string -> typ
  val read_const_proper: Proof.context -> string -> term
  val read_const: Proof.context -> string -> term
  val allow_dummies: Proof.context -> Proof.context
  val decode_term: Proof.context -> term -> term
  val standard_infer_types: Proof.context -> term list -> term list
  val read_term_pattern: Proof.context -> string -> term
  val read_term_schematic: Proof.context -> string -> term
  val read_term_abbrev: Proof.context -> string -> term
  val expand_abbrevs: Proof.context -> term -> term
  val cert_term: Proof.context -> term -> term
  val cert_prop: Proof.context -> term -> term
  val goal_export: Proof.context -> Proof.context -> thm list -> thm list
  val export: Proof.context -> Proof.context -> thm list -> thm list
  val export_morphism: Proof.context -> Proof.context -> morphism
  val norm_export_morphism: Proof.context -> Proof.context -> morphism
  val add_binds: (indexname * string option) list -> Proof.context -> Proof.context
  val add_binds_i: (indexname * term option) list -> Proof.context -> Proof.context
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
  val add_path: string -> Proof.context -> Proof.context
  val no_base_names: Proof.context -> Proof.context
  val qualified_names: Proof.context -> Proof.context
  val sticky_prefix: string -> Proof.context -> Proof.context
  val restore_naming: Proof.context -> Proof.context -> Proof.context
  val reset_naming: Proof.context -> Proof.context
  val note_thmss: string -> (Thm.binding * (Facts.ref * attribute list) list) list ->
    Proof.context -> (string * thm list) list * Proof.context
  val note_thmss_i: string -> (Thm.binding * (thm list * attribute list) list) list ->
    Proof.context -> (string * thm list) list * Proof.context
  val put_thms: bool -> string * thm list option -> Proof.context -> Proof.context
  val read_vars: (binding * string option * mixfix) list -> Proof.context ->
    (binding * typ option * mixfix) list * Proof.context
  val cert_vars: (binding * typ option * mixfix) list -> Proof.context ->
    (binding * typ option * mixfix) list * Proof.context
  val add_fixes: (binding * string option * mixfix) list ->
    Proof.context -> string list * Proof.context
  val add_fixes_i: (binding * typ option * mixfix) list ->
    Proof.context -> string list * Proof.context
  val auto_fixes: Proof.context * (term list list * 'a) -> Proof.context * (term list list * 'a)
  val bind_fixes: string list -> Proof.context -> (term -> term) * Proof.context
  val add_assms: Assumption.export ->
    (Thm.binding * (string * string list) list) list ->
    Proof.context -> (string * thm list) list * Proof.context
  val add_assms_i: Assumption.export ->
    (Thm.binding * (term * term list) list) list ->
    Proof.context -> (string * thm list) list * Proof.context
  val add_cases: bool -> (string * RuleCases.T option) list -> Proof.context -> Proof.context
  val apply_case: RuleCases.T -> Proof.context -> (string * term list) list * Proof.context
  val get_case: Proof.context -> string -> string option list -> RuleCases.T
  val notation: bool -> Syntax.mode -> (term * mixfix) list -> Proof.context -> Proof.context
  val target_notation: bool -> Syntax.mode -> (term * mixfix) list -> morphism ->
    Context.generic -> Context.generic
  val add_const_constraint: string * typ option -> Proof.context -> Proof.context
  val add_abbrev: string -> Properties.T ->
    binding * term -> Proof.context -> (term * term) * Proof.context
  val revert_abbrev: string -> string -> Proof.context -> Proof.context
  val verbose: bool ref
  val setmp_verbose: ('a -> 'b) -> 'a -> 'b
  val print_syntax: Proof.context -> unit
  val print_abbrevs: Proof.context -> unit
  val print_binds: Proof.context -> unit
  val print_lthms: Proof.context -> unit
  val print_cases: Proof.context -> unit
  val debug: bool ref
  val prems_limit: int ref
  val pretty_ctxt: Proof.context -> Pretty.T list
  val pretty_context: Proof.context -> Pretty.T list
  val query_type: Proof.context -> string -> Properties.T
  val query_const: Proof.context -> string -> Properties.T
  val query_class: Proof.context -> string -> Properties.T
end;

structure ProofContext: PROOF_CONTEXT =
struct

val theory_of = Context.theory_of_proof;
val init = Context.init_proof;


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
   {mode: mode,                                       (*inner syntax mode*)
    naming: NameSpace.naming,                         (*local naming conventions*)
    syntax: LocalSyntax.T,                            (*local syntax*)
    consts: Consts.T * Consts.T,                      (*local/global consts*)
    facts: Facts.T,                                   (*local facts*)
    cases: (string * (RuleCases.T * bool)) list};     (*named case contexts*)

fun make_ctxt (mode, naming, syntax, consts, facts, cases) =
  Ctxt {mode = mode, naming = naming, syntax = syntax,
    consts = consts, facts = facts, cases = cases};

val local_naming = NameSpace.default_naming |> NameSpace.add_path "local";

structure ContextData = ProofDataFun
(
  type T = ctxt;
  fun init thy =
    make_ctxt (mode_default, local_naming, LocalSyntax.init thy,
      (Sign.consts_of thy, Sign.consts_of thy), Facts.empty, []);
);

fun rep_context ctxt = ContextData.get ctxt |> (fn Ctxt args => args);

fun map_context f =
  ContextData.map (fn Ctxt {mode, naming, syntax, consts, facts, cases} =>
    make_ctxt (f (mode, naming, syntax, consts, facts, cases)));

fun set_mode mode = map_context (fn (_, naming, syntax, consts, facts, cases) =>
  (mode, naming, syntax, consts, facts, cases));

fun map_mode f =
  map_context (fn (Mode {stmt, pattern, schematic, abbrev}, naming, syntax, consts, facts, cases) =>
    (make_mode (f (stmt, pattern, schematic, abbrev)), naming, syntax, consts, facts, cases));

fun map_naming f =
  map_context (fn (mode, naming, syntax, consts, facts, cases) =>
    (mode, f naming, syntax, consts, facts, cases));

fun map_syntax f =
  map_context (fn (mode, naming, syntax, consts, facts, cases) =>
    (mode, naming, f syntax, consts, facts, cases));

fun map_consts f =
  map_context (fn (mode, naming, syntax, consts, facts, cases) =>
    (mode, naming, syntax, f consts, facts, cases));

fun map_facts f =
  map_context (fn (mode, naming, syntax, consts, facts, cases) =>
    (mode, naming, syntax, consts, f facts, cases));

fun map_cases f =
  map_context (fn (mode, naming, syntax, consts, facts, cases) =>
    (mode, naming, syntax, consts, facts, f cases));

val get_mode = #mode o rep_context;
val restore_mode = set_mode o get_mode;
val abbrev_mode = get_mode #> (fn Mode {abbrev, ...} => abbrev);

fun set_stmt stmt =
  map_mode (fn (_, pattern, schematic, abbrev) => (stmt, pattern, schematic, abbrev));

val naming_of = #naming o rep_context;
val full_name = NameSpace.full_name o naming_of;

val syntax_of = #syntax o rep_context;
val syn_of = LocalSyntax.syn_of o syntax_of;
val set_syntax_mode = map_syntax o LocalSyntax.set_mode;
val restore_syntax_mode = map_syntax o LocalSyntax.restore_mode o syntax_of;

val consts_of = #1 o #consts o rep_context;
val const_syntax_name = Consts.syntax_name o consts_of;
val the_const_constraint = Consts.the_constraint o consts_of;

fun mk_const ctxt (c, Ts) = Const (c, Consts.instance (consts_of ctxt) (c, Ts));

val facts_of = #facts o rep_context;
val cases_of = #cases o rep_context;


(* theory transfer *)

fun transfer_syntax thy =
  map_syntax (LocalSyntax.rebuild thy) #>
  map_consts (fn (local_consts, _) =>
    let val thy_consts = Sign.consts_of thy
    in (Consts.merge (local_consts, thy_consts), thy_consts) end);

fun transfer thy = Context.transfer_proof thy #> transfer_syntax thy;

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

fun pretty_thm_legacy th =
  let val thy = Thm.theory_of_thm th
  in Display.pretty_thm_aux (Syntax.pp_global thy) true false [] th end;

fun pretty_thm ctxt th =
  let val asms = map Thm.term_of (Assumption.assms_of ctxt)
  in Display.pretty_thm_aux (Syntax.pp ctxt) false true asms th end;

fun pretty_thms ctxt [th] = pretty_thm ctxt th
  | pretty_thms ctxt ths = Pretty.blk (0, Pretty.fbreaks (map (pretty_thm ctxt) ths));

fun pretty_fact_name ctxt a = Pretty.block
  [Pretty.markup (Markup.fact a) [Pretty.str (extern_fact ctxt a)], Pretty.str ":"];

fun pretty_fact ctxt ("", ths) = pretty_thms ctxt ths
  | pretty_fact ctxt (a, [th]) = Pretty.block
      [pretty_fact_name ctxt a, Pretty.brk 1, pretty_thm ctxt th]
  | pretty_fact ctxt (a, ths) = Pretty.block
      (Pretty.fbreaks (pretty_fact_name ctxt a :: map (pretty_thm ctxt) ths));

val string_of_thm = Pretty.string_of oo pretty_thm;



(** prepare types **)

(* read_typ *)

fun read_typ_mode mode ctxt s =
  Syntax.read_typ (Type.set_mode mode ctxt) s;

val read_typ        = read_typ_mode Type.mode_default;
val read_typ_syntax = read_typ_mode Type.mode_syntax;
val read_typ_abbrev = read_typ_mode Type.mode_abbrev;


(* cert_typ *)

fun cert_typ_mode mode ctxt T =
  Sign.certify_typ_mode mode (theory_of ctxt) T
    handle TYPE (msg, _, _) => error msg;

val cert_typ        = cert_typ_mode Type.mode_default;
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
          (Pretty.str (setmp show_question_marks true Term.string_of_vname (x', i))))
  | NONE => Pretty.mark Markup.var (Pretty.str s));

fun class_markup _ c =    (* FIXME authentic name *)
  Pretty.mark (Markup.tclassN, []) (Pretty.str c);

fun plain_markup m _ s = Pretty.mark m (Pretty.str s);

val token_trans =
 Syntax.tokentrans_mode ""
  [("class", class_markup),
   ("tfree", plain_markup Markup.tfree),
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

val token_content = Syntax.read_token #>> SymbolPos.content;

fun prep_const_proper ctxt (c, pos) =
  let val t as (Const (d, _)) =
    (case Variable.lookup_const ctxt c of
      SOME d => Const (d, Consts.type_scheme (consts_of ctxt) d handle TYPE (msg, _, _) => error msg)
    | NONE => Consts.read_const (consts_of ctxt) c)
  in Position.report (Markup.const d) pos; t end;

in

fun read_tyname ctxt str =
  let
    val thy = theory_of ctxt;
    val (c, pos) = token_content str;
  in
    if Syntax.is_tid c then
     (Position.report Markup.tfree pos;
      TFree (c, the_default (Sign.defaultS thy) (Variable.def_sort ctxt (c, ~1))))
    else
      let
        val d = Sign.intern_type thy c;
        val _ = Position.report (Markup.tycon d) pos;
      in Type (d, replicate (Sign.arity_number thy d) dummyT) end
  end;

fun read_const_proper ctxt = prep_const_proper ctxt o token_content;

fun read_const ctxt str =
  let val (c, pos) = token_content str in
    (case (lookup_skolem ctxt c, Variable.is_const ctxt c) of
      (SOME x, false) =>
        (Position.report (Markup.name x
            (if can Name.dest_skolem x then Markup.skolem else Markup.free)) pos;
          Free (x, infer_type ctxt x))
    | _ => prep_const_proper ctxt (c, pos))
  end;

end;


(* read_term *)

fun read_term_mode mode ctxt = Syntax.read_term (set_mode mode ctxt);

val read_term_pattern   = read_term_mode mode_pattern;
val read_term_schematic = read_term_mode mode_schematic;
val read_term_abbrev    = read_term_mode mode_abbrev;


(* local abbreviations *)

val tsig_of = Sign.tsig_of o ProofContext.theory_of;

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
  in
    if abbrev orelse print_mode_active "no_abbrevs" orelse not (can Term.type_of t) then t
    else t |> Pattern.rewrite_term thy (Consts.abbrevs_of consts (print_mode_value () @ [""])) []
  end;


(* patterns *)

fun prepare_patternT ctxt =
  let val Mode {pattern, schematic, ...} = get_mode ctxt in
    if pattern orelse schematic then I
    else Term.map_atyps
      (fn T as TVar (xi, _) =>
            if not (TypeInfer.is_param xi)
            then error ("Illegal schematic type variable: " ^ Term.string_of_vname xi)
            else T
        | T => T)
  end;


local

structure AllowDummies = ProofDataFun(type T = bool fun init _ = false);

fun check_dummies ctxt t =
  if AllowDummies.get ctxt then t
  else Term.no_dummy_patterns t handle TERM _ => error "Illegal dummy pattern(s) in term";

fun prepare_dummies ts = #1 (fold_map Term.replace_dummy_patterns ts 1);

in

val allow_dummies = AllowDummies.put true;

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

fun get_sort thy def_sort raw_env =
  let
    val tsig = Sign.tsig_of thy;

    fun eq ((xi, S), (xi', S')) =
      Term.eq_ix (xi, xi') andalso Type.eq_sort tsig (S, S');
    val env = distinct eq raw_env;
    val _ = (case duplicates (eq_fst (op =)) env of [] => ()
      | dups => error ("Inconsistent sort constraints for type variable(s) "
          ^ commas_quote (map (Term.string_of_vname' o fst) dups)));

    fun get xi =
      (case (AList.lookup (op =) env xi, def_sort xi) of
        (NONE, NONE) => Type.defaultS tsig
      | (NONE, SOME S) => S
      | (SOME S, NONE) => S
      | (SOME S, SOME S') =>
          if Type.eq_sort tsig (S, S') then S'
          else error ("Sort constraint inconsistent with default for type variable " ^
            quote (Term.string_of_vname' xi)));
  in get end;

local

fun intern_skolem ctxt def_type x =
  let
    val _ = no_skolem false x;
    val sko = lookup_skolem ctxt x;
    val is_const = can (read_const_proper ctxt) x orelse NameSpace.is_qualified x;
    val is_declared = is_some (def_type (x, ~1));
  in
    if Variable.is_const ctxt x then NONE
    else if is_some sko then sko
    else if not is_const orelse is_declared then SOME x
    else NONE
  end;

in

fun term_context ctxt =
  let val thy = theory_of ctxt in
   {get_sort = get_sort thy (Variable.def_sort ctxt),
    map_const = fn a => ((true, #1 (Term.dest_Const (read_const_proper ctxt a)))
      handle ERROR _ => (false, Consts.intern (consts_of ctxt) a)),
    map_free = intern_skolem ctxt (Variable.def_type ctxt false),
    map_type = Sign.intern_tycons thy,
    map_sort = Sign.intern_sort thy}
  end;

fun decode_term ctxt =
  let val {get_sort, map_const, map_free, map_type, map_sort} = term_context ctxt
  in Syntax.decode_term get_sort map_const map_free map_type map_sort end;

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

fun standard_infer_types ctxt ts =
  let val Mode {pattern, ...} = get_mode ctxt in
    TypeInfer.infer_types (Syntax.pp ctxt) (tsig_of ctxt) (Syntax.check_typs ctxt)
      (try (Consts.the_constraint (consts_of ctxt))) (Variable.def_type ctxt pattern)
      (Variable.names_of ctxt) (Variable.maxidx_of ctxt) ts
    handle TYPE (msg, _, _) => error msg
  end;

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
    val S = Syntax.standard_parse_sort ctxt (syn_of ctxt)
        (Sign.intern_sort (theory_of ctxt)) (syms, pos)
      handle ERROR msg => cat_error msg  ("Failed to parse sort" ^ Position.str_of pos)
  in S end;

fun parse_typ ctxt text =
  let
    val thy = ProofContext.theory_of ctxt;
    val get_sort = get_sort thy (Variable.def_sort ctxt);

    val (syms, pos) = Syntax.parse_token Markup.typ text;
    val T = Sign.intern_tycons thy
        (Syntax.standard_parse_typ ctxt (syn_of ctxt) get_sort (Sign.intern_sort thy) (syms, pos))
      handle ERROR msg => cat_error msg  ("Failed to parse type" ^ Position.str_of pos);
  in T end;

fun parse_term T ctxt text =
  let
    val thy = theory_of ctxt;
    val {get_sort, map_const, map_free, map_type, map_sort} = term_context ctxt;

    val (T', _) = TypeInfer.paramify_dummies T 0;
    val (markup, kind) = if T' = propT then (Markup.prop, "proposition") else (Markup.term, "term");
    val (syms, pos) = Syntax.parse_token markup text;

    fun check t = (Syntax.check_term ctxt (TypeInfer.constrain T' t); NONE)
      handle ERROR msg => SOME msg;
    val t = Syntax.standard_parse_term (Syntax.pp ctxt) check get_sort map_const map_free
        map_type map_sort ctxt (Sign.is_logtype thy) (syn_of ctxt) T' (syms, pos)
      handle ERROR msg => cat_error msg  ("Failed to parse " ^ kind ^ Position.str_of pos);
  in t end;


fun unparse_sort ctxt S =
  Syntax.standard_unparse_sort ctxt (syn_of ctxt) (Sign.extern_sort (theory_of ctxt) S);

fun unparse_typ ctxt T =
  Syntax.standard_unparse_typ ctxt (syn_of ctxt) (Sign.extern_typ (theory_of ctxt) T);

fun unparse_term ctxt t =
  let
    val thy = theory_of ctxt;
    val syntax = syntax_of ctxt;
    val consts = consts_of ctxt;
  in
    t
    |> Sign.extern_term (Consts.extern_early consts) thy
    |> LocalSyntax.extern_term syntax
    |> Syntax.standard_unparse_term (Consts.extern consts) ctxt (LocalSyntax.syn_of syntax)
        (not (PureThy.old_appl_syntax thy))
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



(** bindings **)

(* simult_matches *)

fun simult_matches ctxt (t, pats) =
  (case Seq.pull (Unify.matchers (theory_of ctxt) (map (rpair t) pats)) of
    NONE => error "Pattern match failed!"
  | SOME (env, _) => map (apsnd snd) (Envir.alist_of env));


(* add_binds(_i) *)

local

fun gen_bind prep (xi as (x, _), raw_t) ctxt =
  ctxt
  |> Variable.add_binds [(xi, Option.map (prep (set_mode mode_default ctxt)) raw_t)];

in

fun drop_schematic (b as (xi, SOME t)) = if Term.exists_subterm is_Var t then (xi, NONE) else b
  | drop_schematic b = b;

val add_binds = fold (gen_bind Syntax.read_term);
val add_binds_i = fold (gen_bind cert_term);

fun auto_bind f ts ctxt = ctxt |> add_binds_i (map drop_schematic (f (theory_of ctxt) ts));
val auto_bind_goal = auto_bind AutoBind.goal;
val auto_bind_facts = auto_bind AutoBind.facts;

end;


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
          ctxt (*sic!*) |> fold Variable.declare_term (map #2 binds') |> add_binds_i binds''
        else ctxt' |> add_binds_i binds'');
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
    fun gen_binds c = c |> add_binds_i (map #1 binds ~~ map SOME (gen (map #2 binds)));
  in (ctxt' |> add_binds_i (map (apsnd SOME) binds), (propss, gen_binds)) end;

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
          Goal.prove ctxt [] [] prop (K (ALLGOALS (fact_tac [th])))
          |> Thm.default_position_of th;
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


(* name space operations *)

val add_path        = map_naming o NameSpace.add_path;
val no_base_names   = map_naming NameSpace.no_base_names;
val qualified_names = map_naming NameSpace.qualified_names;
val sticky_prefix   = map_naming o NameSpace.sticky_prefix;
val restore_naming  = map_naming o K o naming_of;
val reset_naming    = map_naming (K local_naming);


(* facts *)

local

fun update_thms _ (b, NONE) ctxt = ctxt |> map_facts (Facts.del (full_name ctxt b))
  | update_thms do_props (b, SOME ths) ctxt = ctxt |> map_facts
      (Facts.add_local do_props (naming_of ctxt) (b, ths) #> snd);

fun gen_note_thmss get k = fold_map (fn ((b, more_attrs), raw_facts) => fn ctxt =>
  let
    val pos = Binding.pos_of b;
    val name = full_name ctxt b;
    val _ = ContextPosition.report_visible ctxt (Markup.local_fact_decl name) pos;

    val facts = PureThy.name_thmss false pos name (map (apfst (get ctxt)) raw_facts);
    fun app (th, attrs) x =
      swap (Library.foldl_map (Thm.proof_attributes (surround (Thm.kind k) (attrs @ more_attrs))) (x, th));
    val (res, ctxt') = fold_map app facts ctxt;
    val thms = PureThy.name_thms false false pos name (flat res);
    val Mode {stmt, ...} = get_mode ctxt;
  in ((name, thms), ctxt' |> update_thms stmt (b, SOME thms)) end);

in

fun note_thmss k = gen_note_thmss get_fact k;
fun note_thmss_i k = gen_note_thmss (K I) k;

fun put_thms do_props thms ctxt = ctxt
  |> map_naming (K local_naming)
  |> ContextPosition.set_visible false
  |> update_thms do_props (apfst Binding.name thms)
  |> ContextPosition.restore_visible ctxt
  |> restore_naming ctxt;

end;



(** parameters **)

(* variables *)

fun declare_var (x, opt_T, mx) ctxt =
  let val T = (case opt_T of SOME T => T | NONE => Syntax.mixfixT mx)
  in ((x, T, mx), ctxt |> Variable.declare_constraints (Free (x, T))) end;

local

fun prep_vars prep_typ internal =
  fold_map (fn (raw_b, raw_T, raw_mx) => fn ctxt =>
    let
      val raw_x = Binding.name_of raw_b;
      val (x, mx) = Syntax.const_mixfix raw_x raw_mx;
      val _ = Syntax.is_identifier (no_skolem internal x) orelse
        error ("Illegal variable name: " ^ quote x);

      fun cond_tvars T =
        if internal then T
        else Type.no_tvars T handle TYPE (msg, _, _) => error msg;
      val opt_T = Option.map (cond_tvars o cert_typ ctxt o prep_typ ctxt) raw_T;
      val var = (Binding.map_name (K x) raw_b, opt_T, mx);
    in (var, ctxt |> declare_var (x, opt_T, mx) |> #2) end);

in

val read_vars = prep_vars Syntax.parse_typ false;
val cert_vars = prep_vars (K I) true;

end;


(* authentic constants *)

local

fun const_ast_tr intern ctxt [Syntax.Variable c] =
      let
        val Const (c', _) = read_const_proper ctxt c;
        val d = if intern then const_syntax_name ctxt c' else c;
      in Syntax.Constant d end
  | const_ast_tr _ _ asts = raise Syntax.AST ("const_ast_tr", asts);

in

val _ = Context.>> (Context.map_theory
 (Sign.add_syntax
   [("_context_const", "id => logic", Delimfix "CONST _"),
    ("_context_const", "id => aprop", Delimfix "CONST _"),
    ("_context_const", "longid => logic", Delimfix "CONST _"),
    ("_context_const", "longid => aprop", Delimfix "CONST _"),
    ("_context_xconst", "id => logic", Delimfix "XCONST _"),
    ("_context_xconst", "id => aprop", Delimfix "XCONST _"),
    ("_context_xconst", "longid => logic", Delimfix "XCONST _"),
    ("_context_xconst", "longid => aprop", Delimfix "XCONST _")] #>
  Sign.add_advanced_trfuns
    ([("_context_const", const_ast_tr true), ("_context_xconst", const_ast_tr false)], [], [], [])));

end;


(* notation *)

local

fun const_syntax ctxt (Free (x, T), mx) = SOME (true, (x, T, mx))
  | const_syntax ctxt (Const (c, _), mx) =
      Option.map (pair false) (try (Consts.syntax (consts_of ctxt)) (c, mx))
  | const_syntax _ _ = NONE;

in

fun notation add mode args ctxt =
  ctxt |> map_syntax
    (LocalSyntax.update_modesyntax (theory_of ctxt) add mode (map_filter (const_syntax ctxt) args));

fun target_notation add mode args phi =
  let val args' = filter (fn (t, _) => Type.similar_types (t, Morphism.term phi t)) args;
  in Context.mapping (Sign.notation add mode args') (notation add mode args') end;

end;


(* local constants *)

fun add_const_constraint (c, opt_T) ctxt =
  let
    fun prepT raw_T =
      let val T = cert_typ ctxt raw_T
      in cert_term ctxt (Const (c, T)); T end;
  in ctxt |> (map_consts o apfst) (Consts.constrain (c, Option.map prepT opt_T)) end;

fun add_abbrev mode tags (b, raw_t) ctxt =
  let
    val t0 = cert_term (ctxt |> set_mode mode_abbrev) raw_t
      handle ERROR msg => cat_error msg ("in constant abbreviation " ^ quote (Binding.str_of b));
    val [t] = Variable.exportT_terms (Variable.declare_term t0 ctxt) ctxt [t0];
    val ((lhs, rhs), consts') = consts_of ctxt
      |> Consts.abbreviate (Syntax.pp ctxt) (tsig_of ctxt) (naming_of ctxt) mode tags (b, t);
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
  else (true, (x, T, mx));

fun gen_fixes prep raw_vars ctxt =
  let
    val (vars, _) = prep raw_vars ctxt;
    val (xs', ctxt') = Variable.add_fixes (map (Binding.name_of o #1) vars) ctxt;
    val ctxt'' =
      ctxt'
      |> fold_map declare_var (map2 (fn x' => fn (_, T, mx) => (x', T, mx)) xs' vars)
      |-> (map_syntax o LocalSyntax.add_syntax (theory_of ctxt) o map prep_mixfix);
    val _ = (vars ~~ xs') |> List.app (fn ((b, _, _), x') =>
      ContextPosition.report_visible ctxt (Markup.fixed_decl x') (Binding.pos_of b));
  in (xs', ctxt'') end;

in

val add_fixes = gen_fixes read_vars;
val add_fixes_i = gen_fixes cert_vars;

end;


(* fixes vs. frees *)

fun auto_fixes (arg as (ctxt, (propss, x))) =
  ((fold o fold) Variable.auto_fixes propss ctxt, (propss, x));

fun bind_fixes xs ctxt =
  let
    val (_, ctxt') = ctxt |> add_fixes_i (map (fn x => (Binding.name x, NONE, NoSyn)) xs);
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
    |> note_thmss_i Thm.assumptionK (map fst args ~~ map (map (fn th => ([th], []))) premss)
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
    val RuleCases.Case {fixes, assumes, binds, cases} = c;
    val fixes' = replace fxs fixes;
    val binds' = map drop_schematic binds;
  in
    if null (fold (Term.add_tvarsT o snd) fixes []) andalso
      null (fold (fold Term.add_vars o snd) assumes []) then
        RuleCases.Case {fixes = fixes', assumes = assumes, binds = binds', cases = cases}
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
    val RuleCases.Case {fixes, ...} = c;
    val (ts, ctxt') = ctxt |> fold_map fix fixes;
    val RuleCases.Case {assumes, binds, cases, ...} = RuleCases.apply ts c;
  in
    ctxt'
    |> add_binds_i (map drop_schematic binds)
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

val debug = ref false;

val verbose = ref false;
fun verb f x = if ! verbose then f (x ()) else [];

fun setmp_verbose f x = Library.setmp verbose true f x;


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
    val abbrevs = NameSpace.extern_table (space, Symtab.make (Symtab.fold add_abbr consts []));
  in
    if null abbrevs andalso not (! verbose) then []
    else [Pretty.big_list "abbreviations:" (map (pretty_term_abbrev ctxt o #2) abbrevs)]
  end;

val print_abbrevs = Pretty.writeln o Pretty.chunks o pretty_abbrevs true;


(* term bindings *)

fun pretty_binds ctxt =
  let
    val binds = Variable.binds_of ctxt;
    fun prt_bind (xi, (T, t)) = pretty_term_abbrev ctxt (Logic.mk_equals (Var (xi, T), t));
  in
    if Vartab.is_empty binds andalso not (! verbose) then []
    else [Pretty.big_list "term bindings:" (map prt_bind (Vartab.dest binds))]
  end;

val print_binds = Pretty.writeln o Pretty.chunks o pretty_binds;


(* local theorems *)

fun pretty_lthms ctxt =
  let
    val local_facts = facts_of ctxt;
    val props = Facts.props local_facts;
    val facts =
      (if null props then [] else [("unnamed", props)]) @
      Facts.dest_static [] local_facts;
  in
    if null facts andalso not (! verbose) then []
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
      | prt_sect s sep prt xs = [Pretty.block (Pretty.breaks (Pretty.str s ::
            flat (Library.separate sep (map (Library.single o prt) xs))))];
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
      | add_case (name, (c as RuleCases.Case {fixes, ...}, true)) =
          cons (name, (fixes, case_result c ctxt));
    val cases = fold add_case (cases_of ctxt) [];
  in
    if null cases andalso not (! verbose) then []
    else [Pretty.big_list "cases:" (map pretty_case cases)]
  end;

val print_cases = Pretty.writeln o Pretty.chunks o pretty_cases;

end;


(* core context *)

val prems_limit = ref ~1;

fun pretty_ctxt ctxt =
  if ! prems_limit < 0 andalso not (! debug) then []
  else
    let
      val prt_term = Syntax.pretty_term ctxt;

      (*structures*)
      val structs = LocalSyntax.structs_of (syntax_of ctxt);
      val prt_structs = if null structs then []
        else [Pretty.block (Pretty.str "structures:" :: Pretty.brk 1 ::
          Pretty.commas (map Pretty.str structs))];

      (*fixes*)
      fun prt_fix (x, x') =
        if x = x' then Pretty.str x
        else Pretty.block [Pretty.str x, Pretty.str " =", Pretty.brk 1, prt_term (Syntax.free x')];
      val fixes =
        rev (filter_out ((can Name.dest_internal orf member (op =) structs) o #1)
          (Variable.fixes_of ctxt));
      val prt_fixes = if null fixes then []
        else [Pretty.block (Pretty.str "fixed variables:" :: Pretty.brk 1 ::
          Pretty.commas (map prt_fix fixes))];

      (*prems*)
      val prems = Assumption.prems_of ctxt;
      val len = length prems;
      val suppressed = len - ! prems_limit;
      val prt_prems = if null prems then []
        else [Pretty.big_list "prems:" ((if suppressed <= 0 then [] else [Pretty.str "..."]) @
          map (pretty_thm ctxt) (Library.drop (suppressed, prems)))];
    in prt_structs @ prt_fixes @ prt_prems end;


(* main context *)

fun pretty_context ctxt =
  let
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


(* query meta data *)

val query_type = Type.the_tags o tsig_of;

fun query_const ctxt name =
  Consts.the_tags (consts_of ctxt) name handle TYPE (msg, _, _) => error msg;

fun query_class ctxt name = query_const ctxt (Logic.const_of_class name);

end;
