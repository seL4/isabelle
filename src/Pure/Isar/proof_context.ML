(*  Title:      Pure/Isar/proof_context.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The key concept of Isar proof contexts: elevates primitive local
reasoning Gamma |- phi to a structured concept, with generic context
elements.  See also structure Variable and Assumption.
*)

signature PROOF_CONTEXT =
sig
  val theory_of: Proof.context -> theory
  val init: theory -> Proof.context
  val is_stmt: Proof.context -> bool
  val set_stmt: bool -> Proof.context -> Proof.context
  val restore_stmt: Proof.context -> Proof.context -> Proof.context
  val naming_of: Proof.context -> NameSpace.naming
  val full_name: Proof.context -> bstring -> string
  val consts_of: Proof.context -> Consts.T
  val const_syntax_name: Proof.context -> string -> string
  val set_syntax_mode: Syntax.mode -> Proof.context -> Proof.context
  val restore_syntax_mode: Proof.context -> Proof.context -> Proof.context
  val theorems_of: Proof.context -> thm list NameSpace.table
  val fact_index_of: Proof.context -> FactIndex.T
  val transfer: theory -> Proof.context -> Proof.context
  val theory: (theory -> theory) -> Proof.context -> Proof.context
  val theory_result: (theory -> 'a * theory) -> Proof.context -> 'a * Proof.context
  val pretty_term: Proof.context -> term -> Pretty.T
  val pretty_term_abbrev: Proof.context -> term -> Pretty.T
  val pretty_typ: Proof.context -> typ -> Pretty.T
  val pretty_sort: Proof.context -> sort -> Pretty.T
  val pretty_classrel: Proof.context -> class list -> Pretty.T
  val pretty_arity: Proof.context -> arity -> Pretty.T
  val pp: Proof.context -> Pretty.pp
  val pretty_thm_legacy: thm -> Pretty.T
  val pretty_thm: Proof.context -> thm -> Pretty.T
  val pretty_thms: Proof.context -> thm list -> Pretty.T
  val pretty_fact: Proof.context -> string * thm list -> Pretty.T
  val pretty_proof: Proof.context -> Proofterm.proof -> Pretty.T
  val pretty_proof_of: Proof.context -> bool -> thm -> Pretty.T
  val string_of_typ: Proof.context -> typ -> string
  val string_of_term: Proof.context -> term -> string
  val string_of_thm: Proof.context -> thm -> string
  val read_typ: Proof.context -> string -> typ
  val read_typ_syntax: Proof.context -> string -> typ
  val read_typ_abbrev: Proof.context -> string -> typ
  val cert_typ: Proof.context -> typ -> typ
  val cert_typ_syntax: Proof.context -> typ -> typ
  val cert_typ_abbrev: Proof.context -> typ -> typ
  val get_skolem: Proof.context -> string -> string
  val revert_skolem: Proof.context -> string -> string
  val revert_skolems: Proof.context -> term -> term
  val decode_term: Proof.context -> term -> term
  val read_termTs_schematic: Proof.context -> (string -> bool) -> (indexname -> typ option)
    -> (indexname -> sort option) -> string list -> (string * typ) list
    -> term list * (indexname * typ) list
  val read_prop_legacy: Proof.context -> string -> term
  val read_term: Proof.context -> string -> term
  val read_prop: Proof.context -> string -> term
  val read_prop_schematic: Proof.context -> string -> term
  val read_termTs: Proof.context -> (string * typ) list -> term list
  val read_terms: Proof.context -> string list -> term list
  val read_term_pats: typ -> Proof.context -> string list -> term list
  val read_prop_pats: Proof.context -> string list -> term list
  val read_term_abbrev: Proof.context -> string -> term
  val cert_term: Proof.context -> term -> term
  val cert_terms: Proof.context -> term list -> term list
  val cert_prop: Proof.context -> term -> term
  val cert_term_pats: typ -> Proof.context -> term list -> term list
  val cert_prop_pats: Proof.context -> term list -> term list
  val infer_types: Proof.context -> term list -> term list
  val infer_types_pats: Proof.context -> term list -> term list
  val infer_type: Proof.context -> string -> typ
  val inferred_param: string -> Proof.context -> (string * typ) * Proof.context
  val inferred_fixes: Proof.context -> (string * typ) list * Proof.context
  val read_tyname: Proof.context -> string -> typ
  val read_const: Proof.context -> string -> term
  val goal_export: Proof.context -> Proof.context -> thm list -> thm list
  val export: Proof.context -> Proof.context -> thm list -> thm list
  val export_morphism: Proof.context -> Proof.context -> morphism
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
  val get_thm: Proof.context -> thmref -> thm
  val get_thm_closure: Proof.context -> thmref -> thm
  val get_thms: Proof.context -> thmref -> thm list
  val get_thms_closure: Proof.context -> thmref -> thm list
  val valid_thms: Proof.context -> string * thm list -> bool
  val lthms_containing: Proof.context -> FactIndex.spec -> (string * thm list) list
  val add_path: string -> Proof.context -> Proof.context
  val no_base_names: Proof.context -> Proof.context
  val qualified_names: Proof.context -> Proof.context
  val sticky_prefix: string -> Proof.context -> Proof.context
  val restore_naming: Proof.context -> Proof.context -> Proof.context
  val reset_naming: Proof.context -> Proof.context
  val hide_thms: bool -> string list -> Proof.context -> Proof.context
  val put_thms: string * thm list option -> Proof.context -> Proof.context
  val note_thmss: string ->
    ((bstring * attribute list) * (thmref * attribute list) list) list ->
      Proof.context -> (bstring * thm list) list * Proof.context
  val note_thmss_i: string ->
    ((bstring * attribute list) * (thm list * attribute list) list) list ->
      Proof.context -> (bstring * thm list) list * Proof.context
  val read_vars: (string * string option * mixfix) list -> Proof.context ->
    (string * typ option * mixfix) list * Proof.context
  val cert_vars: (string * typ option * mixfix) list -> Proof.context ->
    (string * typ option * mixfix) list * Proof.context
  val read_vars_legacy: (string * string option * mixfix) list -> Proof.context ->
    (string * typ option * mixfix) list * Proof.context
  val cert_vars_legacy: (string * typ option * mixfix) list -> Proof.context ->
    (string * typ option * mixfix) list * Proof.context
  val add_fixes: (string * string option * mixfix) list ->
    Proof.context -> string list * Proof.context
  val add_fixes_i: (string * typ option * mixfix) list ->
    Proof.context -> string list * Proof.context
  val add_fixes_legacy: (string * typ option * mixfix) list ->
    Proof.context -> string list * Proof.context
  val auto_fixes: Proof.context * (term list list * 'a) -> Proof.context * (term list list * 'a)
  val bind_fixes: string list -> Proof.context -> (term -> term) * Proof.context
  val add_assms: Assumption.export ->
    ((string * attribute list) * (string * string list) list) list ->
    Proof.context -> (bstring * thm list) list * Proof.context
  val add_assms_i: Assumption.export ->
    ((string * attribute list) * (term * term list) list) list ->
    Proof.context -> (bstring * thm list) list * Proof.context
  val add_cases: bool -> (string * RuleCases.T option) list -> Proof.context -> Proof.context
  val apply_case: RuleCases.T -> Proof.context -> (string * term list) list * Proof.context
  val get_case: Proof.context -> string -> string option list -> RuleCases.T
  val add_notation: Syntax.mode -> (term * mixfix) list ->
    Proof.context -> Proof.context
  val target_notation: Syntax.mode -> (term * mixfix) list -> morphism ->
    Context.generic -> Context.generic
  val set_expand_abbrevs: bool -> Proof.context -> Proof.context
  val add_abbrev: string -> bstring * term -> Proof.context -> (term * term) * Proof.context
  val target_abbrev: Syntax.mode -> (string * mixfix) * term -> morphism ->
    Context.generic -> Context.generic
  val local_abbrev: string * term -> Proof.context -> (term * term) * Proof.context
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
end;

structure ProofContext: PROOF_CONTEXT =
struct

val theory_of = Context.theory_of_proof;
val tsig_of = Sign.tsig_of o theory_of;

val init = Context.init_proof;



(** Isar proof context information **)

datatype ctxt =
  Ctxt of
   {is_stmt: bool,                                (*inner statement mode*)
    naming: NameSpace.naming,                     (*local naming conventions*)
    syntax: LocalSyntax.T,                        (*local syntax*)
    consts: Consts.T * Consts.T,                  (*global/local consts*)
    thms: thm list NameSpace.table * FactIndex.T, (*local thms*)
    cases: (string * (RuleCases.T * bool)) list}; (*local contexts*)

fun make_ctxt (is_stmt, naming, syntax, consts, thms, cases) =
  Ctxt {is_stmt = is_stmt, naming = naming, syntax = syntax,
    consts = consts, thms = thms, cases = cases};

val local_naming = NameSpace.default_naming |> NameSpace.add_path "local";

structure ContextData = ProofDataFun
(
  type T = ctxt;
  fun init thy =
    make_ctxt (false, local_naming, LocalSyntax.init thy,
      (Sign.consts_of thy, Sign.consts_of thy),
      (NameSpace.empty_table, FactIndex.empty), []);
);

fun rep_context ctxt = ContextData.get ctxt |> (fn Ctxt args => args);

fun map_context f =
  ContextData.map (fn Ctxt {is_stmt, naming, syntax, consts, thms, cases} =>
    make_ctxt (f (is_stmt, naming, syntax, consts, thms, cases)));

fun set_stmt b =
  map_context (fn (_, naming, syntax, consts, thms, cases) =>
    (b, naming, syntax, consts, thms, cases));

fun map_naming f =
  map_context (fn (is_stmt, naming, syntax, consts, thms, cases) =>
    (is_stmt, f naming, syntax, consts, thms, cases));

fun map_syntax f =
  map_context (fn (is_stmt, naming, syntax, consts, thms, cases) =>
    (is_stmt, naming, f syntax, consts, thms, cases));

fun map_consts f =
  map_context (fn (is_stmt, naming, syntax, consts, thms, cases) =>
    (is_stmt, naming, syntax, f consts, thms, cases));

fun map_thms f =
  map_context (fn (is_stmt, naming, syntax, consts, thms, cases) =>
    (is_stmt, naming, syntax, consts, f thms, cases));

fun map_cases f =
  map_context (fn (is_stmt, naming, syntax, consts, thms, cases) =>
    (is_stmt, naming, syntax, consts, thms, f cases));

val is_stmt = #is_stmt o rep_context;
fun restore_stmt ctxt = set_stmt (is_stmt ctxt);

val naming_of = #naming o rep_context;
val full_name = NameSpace.full o naming_of;

val syntax_of = #syntax o rep_context;
val syn_of = LocalSyntax.syn_of o syntax_of;
val set_syntax_mode = map_syntax o LocalSyntax.set_mode;
val restore_syntax_mode = map_syntax o LocalSyntax.restore_mode o syntax_of;

val consts_of = #2 o #consts o rep_context;
val const_syntax_name = Consts.syntax_name o consts_of;

val thms_of = #thms o rep_context;
val theorems_of = #1 o thms_of;
val fact_index_of = #2 o thms_of;

val cases_of = #cases o rep_context;


(* theory transfer *)

fun transfer_syntax thy =
  map_syntax (LocalSyntax.rebuild thy) #>
  map_consts (fn consts as (global_consts, local_consts) =>
    let val thy_consts = Sign.consts_of thy in
      if Consts.eq_consts (thy_consts, global_consts) then consts
      else (thy_consts, Consts.merge (thy_consts, local_consts))
    end);

fun transfer thy = Context.transfer_proof thy #> transfer_syntax thy;

fun theory f ctxt = transfer (f (theory_of ctxt)) ctxt;

fun theory_result f ctxt =
  let val (res, thy') = f (theory_of ctxt)
  in (res, ctxt |> transfer thy') end;



(** pretty printing **)

local

fun rewrite_term warn thy rews t =
  if can Term.type_of t then Pattern.rewrite_term thy rews [] t
  else (if warn then warning "Printing malformed term -- cannot expand abbreviations" else (); t);

fun pretty_term' abbrevs ctxt t =
  let
    val thy = theory_of ctxt;
    val syntax = syntax_of ctxt;
    val consts = consts_of ctxt;
    val do_abbrevs = abbrevs andalso not (print_mode_active "no_abbrevs");
    val t' = t
      |> do_abbrevs ? rewrite_term true thy (Consts.abbrevs_of consts (! print_mode @ [""]))
      |> do_abbrevs ? rewrite_term false thy (Consts.abbrevs_of consts [Syntax.internalM])
      |> Sign.extern_term (Consts.extern_early consts) thy
      |> LocalSyntax.extern_term syntax;
  in Sign.pretty_term' ctxt (LocalSyntax.syn_of syntax) (Consts.extern consts) t' end;

in

val pretty_term = pretty_term' true;
val pretty_term_abbrev = pretty_term' false;

end;

fun pretty_typ ctxt T = Sign.pretty_typ (theory_of ctxt) T;
fun pretty_sort ctxt S = Sign.pretty_sort (theory_of ctxt) S;
fun pretty_classrel ctxt cs = Sign.pretty_classrel (theory_of ctxt) cs;
fun pretty_arity ctxt ar = Sign.pretty_arity (theory_of ctxt) ar;

fun pp ctxt = Pretty.pp (pretty_term ctxt, pretty_typ ctxt, pretty_sort ctxt,
  pretty_classrel ctxt, pretty_arity ctxt);

fun pretty_thm_legacy th =
  let val thy = Thm.theory_of_thm th
  in Display.pretty_thm_aux (pp (init thy)) true false [] th end;

fun pretty_thm ctxt th =
  let val asms = map Thm.term_of (Assumption.assms_of ctxt)
  in Display.pretty_thm_aux (pp ctxt) false true asms th end;

fun pretty_thms ctxt [th] = pretty_thm ctxt th
  | pretty_thms ctxt ths = Pretty.blk (0, Pretty.fbreaks (map (pretty_thm ctxt) ths));

fun pretty_fact ctxt ("", ths) = pretty_thms ctxt ths
  | pretty_fact ctxt (a, [th]) =
      Pretty.block [Pretty.str (a ^ ":"), Pretty.brk 1, pretty_thm ctxt th]
  | pretty_fact ctxt (a, ths) =
      Pretty.block (Pretty.fbreaks (Pretty.str (a ^ ":") :: map (pretty_thm ctxt) ths));

fun pretty_proof ctxt prf =
  pretty_term_abbrev (ctxt |> transfer_syntax (ProofSyntax.proof_syntax prf (theory_of ctxt)))
    (ProofSyntax.term_of_proof prf);

fun pretty_proof_of ctxt full th =
  pretty_proof ctxt (ProofSyntax.proof_of full th);

val string_of_typ = Pretty.string_of oo pretty_typ;
val string_of_term = Pretty.string_of oo pretty_term;
val string_of_thm = Pretty.string_of oo pretty_thm;



(** prepare types **)

local

fun read_typ_aux read ctxt s =
  read (syn_of ctxt) ctxt (Variable.def_sort ctxt) s;

fun cert_typ_aux cert ctxt raw_T =
  cert (theory_of ctxt) raw_T handle TYPE (msg, _, _) => error msg;

in

val read_typ        = read_typ_aux Sign.read_typ';
val read_typ_syntax = read_typ_aux Sign.read_typ_syntax';
val read_typ_abbrev = read_typ_aux Sign.read_typ_abbrev';
val cert_typ        = cert_typ_aux Sign.certify_typ;
val cert_typ_syntax = cert_typ_aux Sign.certify_typ_syntax;
val cert_typ_abbrev = cert_typ_aux Sign.certify_typ_abbrev;

end;


(* internalize Skolem constants *)

val lookup_skolem = AList.lookup (op =) o Variable.fixes_of;
fun get_skolem ctxt x = the_default x (lookup_skolem ctxt x);

fun no_skolem internal x =
  if can Name.dest_skolem x then
    error ("Illegal reference to internal Skolem constant: " ^ quote x)
  else if not internal andalso can Name.dest_internal x then
    error ("Illegal reference to internal variable: " ^ quote x)
  else x;


(* revert Skolem constants -- approximation only! *)

fun revert_skolem ctxt =
  let
    val rev_fixes = map Library.swap (Variable.fixes_of ctxt);
    val revert = AList.lookup (op =) rev_fixes;
  in
    fn x =>
      (case revert x of
        SOME x' => x'
      | NONE => perhaps (try Name.dest_skolem) x)
   end;

fun revert_skolems ctxt =
  let
    val revert = revert_skolem ctxt;
    fun reverts (Free (x, T)) = Free (revert x, T)
      | reverts (t $ u) = reverts t $ reverts u
      | reverts (Abs (x, T, t)) = Abs (x, T, reverts t)
      | reverts a = a;
  in reverts end



(** prepare terms and propositions **)

(*
  (1) read / certify wrt. theory of context
  (2) intern Skolem constants
  (3) expand term bindings
*)


(* read wrt. theory *)     (*exception ERROR*)

fun read_def_termTs freeze pp syn ctxt (types, sorts, used) fixed sTs =
  Sign.read_def_terms' pp (Sign.is_logtype (theory_of ctxt)) syn (consts_of ctxt) fixed
    ctxt (types, sorts) used freeze sTs;

fun read_def_termT freeze pp syn ctxt defaults fixed sT =
  apfst hd (read_def_termTs freeze pp syn ctxt defaults fixed [sT]);

fun read_term_thy freeze pp syn thy defaults fixed s =
  #1 (read_def_termT freeze pp syn thy defaults fixed (s, dummyT));

fun read_prop_thy freeze pp syn thy defaults fixed s =
  #1 (read_def_termT freeze pp syn thy defaults fixed (s, propT));

fun read_terms_thy freeze pp syn thy defaults fixed =
  #1 o read_def_termTs freeze pp syn thy defaults fixed;

fun read_props_thy freeze pp syn thy defaults fixed =
  #1 o read_def_termTs freeze pp syn thy defaults fixed o map (rpair propT);


(* local abbreviations *)

fun certify_consts ctxt =
  Consts.certify (pp ctxt) (tsig_of ctxt) (consts_of ctxt);

fun reject_schematic (Var (xi, _)) =
      error ("Unbound schematic variable: " ^ Term.string_of_vname xi)
  | reject_schematic (Abs (_, _, t)) = reject_schematic t
  | reject_schematic (t $ u) = (reject_schematic t; reject_schematic u)
  | reject_schematic _ = ();

fun expand_binds ctxt schematic =
  Variable.expand_binds ctxt #> (if schematic then I else tap reject_schematic);


(* schematic type variables *)

val reject_tvars = (Term.map_types o Term.map_atyps)
  (fn TVar (xi, _) => error ("Illegal schematic type variable: " ^ Term.string_of_vname xi)
    | T => T);


(* dummy patterns *)

val prepare_dummies =
  let val next = ref 1 in
    fn t =>
      let val (i, u) = Term.replace_dummy_patterns (! next, t)
      in next := i; u end
  end;

fun reject_dummies t = Term.no_dummy_patterns t
  handle TERM _ => error "Illegal dummy pattern(s) in term";


(* decoding raw terms (syntax trees) *)

fun legacy_intern_skolem ctxt internal def_type x =    (* FIXME cleanup this mess *)
  let
    val sko = lookup_skolem ctxt x;
    val is_const = can (Consts.read_const (consts_of ctxt)) x;
    val is_free = is_some sko orelse not is_const;
    val is_internal = internal x;
    val is_declared = is_some (def_type (x, ~1));
    val res =
      if is_free andalso not is_internal then (no_skolem false x; sko)
      else ((no_skolem false x; ()) handle ERROR msg => legacy_feature msg;
        if is_internal andalso is_declared then SOME x else NONE);
  in if is_some res then res else if is_declared then SOME x else NONE end;

fun decode_term ctxt =
  let
    val thy = theory_of ctxt;
    val get_sort = Sign.get_sort thy (Variable.def_sort ctxt);
    val map_const = try (#1 o Term.dest_Const o Consts.read_const (consts_of ctxt));
    val map_free = legacy_intern_skolem ctxt (K false) (Variable.def_type ctxt false);
    val map_type = Sign.intern_tycons thy;
    val map_sort = Sign.intern_sort thy;
  in Syntax.decode_term get_sort map_const map_free map_type map_sort end;


(* read terms *)

local

fun append_env e1 e2 x = (case e2 x of NONE => e1 x | some => some);

fun gen_read' read app pattern schematic
    ctxt internal more_types more_sorts more_used s =
  let
    val types = append_env (Variable.def_type ctxt pattern) more_types;
    val sorts = append_env (Variable.def_sort ctxt) more_sorts;
    val used = fold Name.declare more_used (Variable.names_of ctxt);
  in
    (read (pp ctxt) (syn_of ctxt) ctxt (types, sorts, used)
        (legacy_intern_skolem ctxt internal types) s
      handle TERM (msg, _) => error msg)
    |> app (certify_consts ctxt)
    |> app (if pattern then I else expand_binds ctxt schematic)
    |> app (if pattern orelse schematic then I else reject_tvars)
    |> app (if pattern then prepare_dummies else reject_dummies)
  end;

fun gen_read read app pattern schematic ctxt =
  gen_read' read app pattern schematic ctxt (K false) (K NONE) (K NONE) [];

in

val read_termTs_schematic = gen_read' (read_def_termTs false) (apfst o map) false true;

fun read_term_pats T ctxt =
  #1 o gen_read (read_def_termTs false) (apfst o map) true false ctxt o map (rpair T);
val read_prop_pats = read_term_pats propT;

fun read_prop_legacy ctxt =
  gen_read' (read_prop_thy true) I false false ctxt (K true) (K NONE) (K NONE) [];

val read_term            = gen_read (read_term_thy true) I false false;
val read_prop            = gen_read (read_prop_thy true) I false false;
val read_prop_schematic  = gen_read (read_prop_thy true) I false true;
val read_termTs          = gen_read (read_terms_thy true) map false false;
fun read_terms ctxt      = read_termTs ctxt o map (rpair dummyT);
fun read_props schematic = gen_read (read_props_thy true) map false schematic;

end;


(* certify terms *)

local

fun gen_cert prop pattern schematic ctxt t = t
  |> certify_consts ctxt
  |> (if pattern then I else expand_binds ctxt schematic)
  |> (fn t' => #1 (Sign.certify' false prop (pp ctxt) (consts_of ctxt) (theory_of ctxt) t')
    handle TYPE (msg, _, _) => error msg
      | TERM (msg, _) => error msg);

in

val cert_term = gen_cert false false false;
val cert_terms = map o cert_term;
val cert_prop = gen_cert true false false;
val cert_props = map oo gen_cert true false;

fun cert_term_pats _ = map o gen_cert false true false;
val cert_prop_pats = map o gen_cert true true false;

end;


(* type inference *)

local

fun gen_infer_types pattern ctxt ts =
  TypeInfer.infer_types (pp ctxt) (tsig_of ctxt) (try (Consts.the_constraint (consts_of ctxt)))
    (Variable.def_type ctxt pattern) (Variable.names_of ctxt) (not pattern) (map (rpair dummyT) ts)
  |> #1 |> map #1;

in

val infer_types = gen_infer_types false;
val infer_types_pats = gen_infer_types true;

end;


(* inferred types of parameters *)

fun infer_type ctxt x =
  Term.fastype_of (singleton (infer_types ctxt) (Free (x, dummyT)));

fun inferred_param x ctxt =
  let val T = infer_type ctxt x
  in ((x, T), ctxt |> Variable.declare_term (Free (x, T))) end;

fun inferred_fixes ctxt =
  fold_map inferred_param (rev (map #2 (Variable.fixes_of ctxt))) ctxt;


(* type and constant names *)

fun read_tyname ctxt c =
  if Syntax.is_tid c then
    TFree (c, the_default (Sign.defaultS (theory_of ctxt)) (Variable.def_sort ctxt (c, ~1)))
  else Sign.read_tyname (theory_of ctxt) c;

fun read_const ctxt c =
  (case lookup_skolem ctxt c of
    SOME x => Free (x, infer_type ctxt x)
  | NONE => Consts.read_const (consts_of ctxt) c);



(** export results **)

fun common_export is_goal inner outer =
  map (Assumption.export is_goal inner outer) #>
  Variable.export inner outer;

val goal_export = common_export true;
val export = common_export false;

fun export_morphism inner outer =
  Assumption.export_morphism inner outer $>
  Variable.export_morphism inner outer;



(** bindings **)

(* simult_matches *)

fun simult_matches ctxt (t, pats) =
  (case Seq.pull (Unify.matchers (theory_of ctxt) (map (rpair t) pats)) of
    NONE => error "Pattern match failed!"
  | SOME (env, _) => map (apsnd snd) (Envir.alist_of env));


(* add_binds(_i) *)

local

fun gen_bind prep (xi as (x, _), raw_t) ctxt =
  ctxt |> Variable.add_binds [(xi, Option.map (prep ctxt) raw_t)];

in

fun drop_schematic (b as (xi, SOME t)) = if Term.exists_subterm is_Var t then (xi, NONE) else b
  | drop_schematic b = b;

val add_binds = fold (gen_bind read_term);
val add_binds_i = fold (gen_bind cert_term);

fun auto_bind f ts ctxt = ctxt |> add_binds_i (map drop_schematic (f (theory_of ctxt) ts));
val auto_bind_goal = auto_bind AutoBind.goal;
val auto_bind_facts = auto_bind AutoBind.facts;

end;


(* match_bind(_i) *)

local

fun prep_bind prep_pats (raw_pats, t) ctxt =
  let
    val ctxt' = Variable.declare_term t ctxt;
    val pats = prep_pats (Term.fastype_of t) ctxt' raw_pats;
    val binds = simult_matches ctxt' (t, pats);
  in (binds, ctxt') end;

fun gen_binds prep_terms prep_pats gen raw_binds ctxt =
  let
    val ts = prep_terms ctxt (map snd raw_binds);
    val (binds, ctxt') =
      apfst flat (fold_map (prep_bind prep_pats) (map fst raw_binds ~~ ts) ctxt);
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

val match_bind = gen_binds read_terms read_term_pats;
val match_bind_i = gen_binds cert_terms cert_term_pats;

end;


(* propositions with patterns *)

local

fun prep_propp schematic prep_props prep_pats (context, args) =
  let
    fun prep (_, raw_pats) (ctxt, prop :: props) =
          let val ctxt' = Variable.declare_term prop ctxt
          in ((prop, prep_pats ctxt' raw_pats), (ctxt', props)) end
      | prep _ _ = sys_error "prep_propp";
    val (propp, (context', _)) = (fold_map o fold_map) prep args
      (context, prep_props schematic context (maps (map fst) args));
  in (context', propp) end;

fun gen_bind_propp prepp (ctxt, raw_args) =
  let
    val (ctxt', args) = prepp (ctxt, raw_args);
    val binds = flat (flat (map (map (simult_matches ctxt')) args));
    val propss = map (map #1) args;

    (*generalize result: context evaluated now, binds added later*)
    val gen = Variable.exportT_terms ctxt' ctxt;
    fun gen_binds c = c |> add_binds_i (map #1 binds ~~ map SOME (gen (map #2 binds)));
  in (ctxt' |> add_binds_i (map (apsnd SOME) binds), (propss, gen_binds)) end;

in

val read_propp = prep_propp false read_props read_prop_pats;
val cert_propp = prep_propp false cert_props cert_prop_pats;
val read_propp_schematic = prep_propp true read_props read_prop_pats;
val cert_propp_schematic = prep_propp true cert_props cert_prop_pats;

val bind_propp = gen_bind_propp read_propp;
val bind_propp_i = gen_bind_propp cert_propp;
val bind_propp_schematic = gen_bind_propp read_propp_schematic;
val bind_propp_schematic_i = gen_bind_propp cert_propp_schematic;

end;



(** theorems **)

(* fact_tac *)

fun comp_incr_tac [] _ st = no_tac st
  | comp_incr_tac (th :: ths) i st =
      (Goal.compose_hhf_tac (Drule.incr_indexes st th) i APPEND comp_incr_tac ths i) st;

fun fact_tac facts = Goal.norm_hhf_tac THEN' comp_incr_tac facts;

fun some_fact_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    val index = fact_index_of ctxt;
    val facts = FactIndex.could_unify index (Term.strip_all_body goal);
  in fact_tac facts i end);


(* get_thm(s) *)

fun retrieve_thms _ pick ctxt (Fact s) =
      let
        val th = Goal.prove ctxt [] [] (read_prop ctxt s) (K (ALLGOALS (some_fact_tac ctxt)))
          handle ERROR msg => cat_error msg "Failed to retrieve literal fact.";
      in pick "" [th] end
  | retrieve_thms from_thy pick ctxt xthmref =
      let
        val thy = theory_of ctxt;
        val (space, tab) = #1 (thms_of ctxt);
        val thmref = PureThy.map_name_of_thmref (NameSpace.intern space) xthmref;
        val name = PureThy.name_of_thmref thmref;
      in
        (case Symtab.lookup tab name of
          SOME ths => map (Thm.transfer thy) (PureThy.select_thm thmref ths)
        | NONE => from_thy thy xthmref) |> pick name
      end;

val get_thm = retrieve_thms PureThy.get_thms PureThy.single_thm;
val get_thm_closure = retrieve_thms PureThy.get_thms_closure PureThy.single_thm;
val get_thms = retrieve_thms PureThy.get_thms (K I);
val get_thms_closure = retrieve_thms PureThy.get_thms_closure (K I);


(* valid_thms *)

fun valid_thms ctxt (name, ths) =
  (case try (fn () => get_thms ctxt (Name name)) () of
    NONE => false
  | SOME ths' => Thm.eq_thms (ths, ths'));


(* lthms_containing *)

fun lthms_containing ctxt spec =
  FactIndex.find (fact_index_of ctxt) spec
  |> map (fn (name, ths) =>
    if valid_thms ctxt (name, ths) then (name, ths)
    else (NameSpace.hidden (if name = "" then "unnamed" else name), ths));


(* name space operations *)

val add_path        = map_naming o NameSpace.add_path;
val no_base_names   = map_naming NameSpace.no_base_names;
val qualified_names = map_naming NameSpace.qualified_names;
val sticky_prefix   = map_naming o NameSpace.sticky_prefix;
val restore_naming  = map_naming o K o naming_of;
val reset_naming    = map_naming (K local_naming);

fun hide_thms fully names = map_thms (fn ((space, tab), index) =>
  ((fold (NameSpace.hide fully) names space, tab), index));


(* put_thms *)

fun update_thms _ ("", NONE) ctxt = ctxt
  | update_thms opts ("", SOME ths) ctxt = ctxt |> map_thms (fn (facts, index) =>
      let
        val index' = uncurry FactIndex.add_local opts ("", ths) index;
      in (facts, index') end)
  | update_thms _ (bname, NONE) ctxt = ctxt |> map_thms (fn ((space, tab), index) =>
      let
        val name = full_name ctxt bname;
        val tab' = Symtab.delete_safe name tab;
      in ((space, tab'), index) end)
  | update_thms opts (bname, SOME ths) ctxt = ctxt |> map_thms (fn ((space, tab), index) =>
      let
        val name = full_name ctxt bname;
        val space' = NameSpace.declare (naming_of ctxt) name space;
        val tab' = Symtab.update (name, ths) tab;
        val index' = uncurry FactIndex.add_local opts (name, ths) index;
      in ((space', tab'), index') end);

fun put_thms thms ctxt =
  ctxt |> map_naming (K local_naming) |> update_thms (true, false) thms |> restore_naming ctxt;


(* note_thmss *)

local

fun gen_note_thmss get k = fold_map (fn ((bname, more_attrs), raw_facts) => fn ctxt =>
  let
    val name = full_name ctxt bname;
    val facts = PureThy.name_thmss false name (map (apfst (get ctxt)) raw_facts);
    fun app (th, attrs) x =
      swap (foldl_map (Thm.proof_attributes (attrs @ more_attrs @ [PureThy.kind k])) (x, th));
    val (res, ctxt') = fold_map app facts ctxt;
    val thms = PureThy.name_thms false false name (flat res);
  in ((bname, thms), ctxt' |> update_thms (is_stmt ctxt, true) (bname, SOME thms)) end);

in

fun note_thmss k = gen_note_thmss get_thms k;
fun note_thmss_i k = gen_note_thmss (K I) k;

end;



(** parameters **)

(* variables *)

fun declare_var (x, opt_T, mx) ctxt =
  let val T = (case opt_T of SOME T => T | NONE => Syntax.mixfixT mx)
  in ((x, T, mx), ctxt |> Variable.declare_constraints (Free (x, T))) end;

local

fun prep_vars prep_typ internal legacy =
  fold_map (fn (raw_x, raw_T, raw_mx) => fn ctxt =>
    let
      val (x, mx) = Syntax.const_mixfix raw_x raw_mx;
      val _ =
        if not legacy andalso not (Syntax.is_identifier (no_skolem internal x)) then
          error ("Illegal variable name: " ^ quote x)
        else ();

      fun cond_tvars T =
        if internal then T
        else Type.no_tvars T handle TYPE (msg, _, _) => error msg;
      val opt_T = Option.map (cond_tvars o prep_typ ctxt) raw_T;
      val var = (x, opt_T, mx);
    in (var, ctxt |> declare_var var |> #2) end);

in

val read_vars        = prep_vars read_typ false false;
val cert_vars        = prep_vars cert_typ true false;
val read_vars_legacy = prep_vars read_typ true true;
val cert_vars_legacy = prep_vars cert_typ true true;

end;


(* authentic constants *)

fun const_syntax ctxt (Free (x, T), mx) = SOME (true, (x, T, mx))
  | const_syntax ctxt (Const (c, _), mx) =
      Option.map (pair false) (try (Consts.syntax (consts_of ctxt)) (c, mx))
  | const_syntax _ _ = NONE;

fun context_const_ast_tr ctxt [Syntax.Variable c] =
      let
        val consts = consts_of ctxt;
        val c' = Consts.intern consts c;
        val _ = Consts.the_constraint consts c' handle TYPE (msg, _, _) => error msg;
      in Syntax.Constant (Syntax.constN ^ c') end
  | context_const_ast_tr _ asts = raise Syntax.AST ("const_ast_tr", asts);

val _ = Context.add_setup
 (Sign.add_syntax
   [("_context_const", "id => 'a", Delimfix "CONST _"),
    ("_context_const", "longid => 'a", Delimfix "CONST _")] #>
  Sign.add_advanced_trfuns ([("_context_const", context_const_ast_tr)], [], [], []));


(* notation *)

fun add_notation mode args ctxt =
  ctxt |> map_syntax
    (LocalSyntax.add_modesyntax (theory_of ctxt) mode (map_filter (const_syntax ctxt) args));

fun target_notation mode args phi =
  let val args' = filter (fn (t, _) => Term.equiv_types (t, Morphism.term phi t)) args;
  in Context.mapping (Sign.add_notation mode args') (add_notation mode args') end;


(* abbreviations *)

val set_expand_abbrevs = map_consts o apsnd o Consts.set_expand;
fun read_term_abbrev ctxt = read_term (set_expand_abbrevs false ctxt);

fun add_abbrev mode (c, raw_t) ctxt =
  let
    val t0 = cert_term (ctxt |> set_expand_abbrevs false) raw_t
      handle ERROR msg => cat_error msg ("in constant abbreviation " ^ quote c);
    val [t] = Variable.exportT_terms (Variable.declare_term t0 ctxt) ctxt [t0];
    val ((lhs, rhs), consts') = consts_of ctxt
      |> Consts.abbreviate (pp ctxt) (tsig_of ctxt) (naming_of ctxt) mode (c, t);
  in
    ctxt
    |> map_consts (apsnd (K consts'))
    |> Variable.declare_term rhs
    |> pair (lhs, rhs)
  end;

fun target_abbrev prmode ((c, mx), rhs) phi =
  let
    val c' = Morphism.name phi c;
    val rhs' = Morphism.term phi rhs;
    val arg' = (c', rhs');
  in
    Context.mapping_result
      (Sign.add_abbrev Syntax.internalM arg') (add_abbrev Syntax.internalM arg')
    #-> (fn (lhs, _) =>
      Term.equiv_types (rhs, rhs') ? Morphism.form (target_notation prmode [(lhs, mx)]))
  end;

fun local_abbrev (x, rhs) =
  Variable.add_fixes [x] #-> (fn [x'] =>
    let
      val T = Term.fastype_of rhs;
      val lhs = Free (x', T);
    in
      Variable.declare_term lhs #>
      Variable.declare_term rhs #>
      Assumption.add_assms (K (K (I, Envir.expand_term_frees [((x', T), rhs)]))) [] #> snd #>
      pair (lhs, rhs)
    end);


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
    val (xs', ctxt') = Variable.add_fixes (map #1 vars) ctxt;
  in
    ctxt'
    |> fold_map declare_var (map2 (fn x' => fn (_, T, mx) => (x', T, mx)) xs' vars)
    |-> (map_syntax o LocalSyntax.add_syntax (theory_of ctxt) o map prep_mixfix)
    |> pair xs'
  end;

in

val add_fixes = gen_fixes read_vars;
val add_fixes_i = gen_fixes cert_vars;
val add_fixes_legacy = gen_fixes cert_vars_legacy;

end;


(* fixes vs. frees *)

fun auto_fixes (arg as (ctxt, (propss, x))) =
  ((fold o fold) Variable.auto_fixes propss ctxt, (propss, x));

fun bind_fixes xs ctxt =
  let
    val (_, ctxt') = ctxt |> add_fixes_i (map (fn x => (x, NONE, NoSyn)) xs);
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
    |> put_thms (AutoBind.premsN, SOME (Assumption.prems_of ctxt2))
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
    val ((_, globals), (space, consts)) =
      pairself (#constants o Consts.dest) (#consts (rep_context ctxt));
    fun add_abbr (_, (_, NONE)) = I
      | add_abbr (c, (T, SOME (t, _))) =
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
    val props = FactIndex.props (fact_index_of ctxt);
    val facts =
      (if null props then I else cons ("unnamed", props))
      (NameSpace.extern_table (#1 (thms_of ctxt)));
  in
    if null facts andalso not (! verbose) then []
    else [Pretty.big_list "facts:" (map (pretty_fact ctxt) facts)]
  end;

val print_lthms = Pretty.writeln o Pretty.chunks o pretty_lthms;


(* local contexts *)

fun pretty_cases ctxt =
  let
    val prt_term = pretty_term ctxt;

    fun prt_let (xi, t) = Pretty.block
      [Pretty.quote (prt_term (Var (xi, Term.fastype_of t))), Pretty.str " =", Pretty.brk 1,
        Pretty.quote (prt_term t)];

    fun prt_asm (a, ts) = Pretty.block (Pretty.breaks
      ((if a = "" then [] else [Pretty.str (a ^ ":")]) @ map (Pretty.quote o prt_term) ts));

    fun prt_sect _ _ _ [] = []
      | prt_sect s sep prt xs = [Pretty.block (Pretty.breaks (Pretty.str s ::
            flat (Library.separate sep (map (Library.single o prt) xs))))];

    fun prt_case (name, (fixes, (asms, (lets, cs)))) = Pretty.block (Pretty.fbreaks
      (Pretty.str (name ^ ":") ::
        prt_sect "fix" [] (Pretty.str o fst) fixes @
        prt_sect "let" [Pretty.str "and"] prt_let
          (map_filter (fn (xi, SOME t) => SOME (xi, t) | _ => NONE) lets) @
        (if forall (null o #2) asms then []
          else prt_sect "assume" [Pretty.str "and"] prt_asm asms) @
        prt_sect "subcases:" [] (Pretty.str o fst) cs));

    fun add_case (_, (_, false)) = I
      | add_case (name, (c as RuleCases.Case {fixes, ...}, true)) =
          cons (name, (fixes, #1 (case_result c ctxt)));
    val cases = fold add_case (cases_of ctxt) [];
  in
    if null cases andalso not (! verbose) then []
    else [Pretty.big_list "cases:" (map prt_case cases)]
  end;

val print_cases = Pretty.writeln o Pretty.chunks o pretty_cases;


(* core context *)

val prems_limit = ref ~1;

fun pretty_ctxt ctxt =
  if ! prems_limit < 0 andalso not (! debug) then []
  else
    let
      val prt_term = pretty_term ctxt;

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
    val prt_term = pretty_term ctxt;
    val prt_typ = pretty_typ ctxt;
    val prt_sort = pretty_sort ctxt;

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
