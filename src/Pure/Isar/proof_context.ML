(*  Title:      Pure/Isar/proof_context.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The key concept of Isar proof contexts.
*)

val show_structs = ref false;

signature PROOF_CONTEXT =
sig
  type context = Context.proof
  type exporter
  exception CONTEXT of string * context
  val theory_of: context -> theory
  val sign_of: context -> theory    (*obsolete*)
  val is_fixed: context -> string -> bool
  val is_known: context -> string -> bool
  val fixed_names_of: context -> string list
  val assumptions_of: context -> (cterm list * exporter) list
  val prems_of: context -> thm list
  val fact_index_of: context -> FactIndex.T
  val init: theory -> context
  val transfer: theory -> context -> context
  val pretty_term: context -> term -> Pretty.T
  val pretty_typ: context -> typ -> Pretty.T
  val pretty_sort: context -> sort -> Pretty.T
  val pp: context -> Pretty.pp
  val pretty_thm: context -> thm -> Pretty.T
  val pretty_thms: context -> thm list -> Pretty.T
  val pretty_fact: context -> string * thm list -> Pretty.T
  val pretty_proof: context -> Proofterm.proof -> Pretty.T
  val pretty_proof_of: context -> bool -> thm -> Pretty.T
  val string_of_typ: context -> typ -> string
  val string_of_term: context -> term -> string
  val default_type: context -> string -> typ option
  val used_types: context -> string list
  val read_typ: context -> string -> typ
  val read_typ_syntax: context -> string -> typ
  val read_typ_abbrev: context -> string -> typ
  val cert_typ: context -> typ -> typ
  val cert_typ_syntax: context -> typ -> typ
  val cert_typ_abbrev: context -> typ -> typ
  val get_skolem: context -> string -> string
  val extern_skolem: context -> term -> term
  val read_termTs: context -> (string -> bool) -> (indexname -> typ option)
    -> (indexname -> sort option) -> string list -> (string * typ) list
    -> term list * (indexname * typ) list
  val read_termTs_schematic: context -> (string -> bool) -> (indexname -> typ option)
    -> (indexname -> sort option) -> string list -> (string * typ) list
    -> term list * (indexname * typ) list
  val read_term_liberal: context -> string -> term
  val read_term: context -> string -> term
  val read_prop: context -> string -> term
  val read_prop_schematic: context -> string -> term
  val read_terms: context -> string list -> term list
  val read_term_pats: typ -> context -> string list -> term list
  val read_prop_pats: context -> string list -> term list
  val cert_term: context -> term -> term
  val cert_prop: context -> term -> term
  val cert_term_pats: typ -> context -> term list -> term list
  val cert_prop_pats: context -> term list -> term list
  val declare_term: term -> context -> context
  val read_tyname: context -> string -> typ
  val read_const: context -> string -> term
  val warn_extra_tfrees: context -> context -> context
  val generalize: context -> context -> term list -> term list
  val find_free: term -> string -> term option
  val export: bool -> context -> context -> thm -> thm Seq.seq
  val export_standard: context -> context -> thm -> thm
  val export_plain: context -> context -> thm -> thm
  val drop_schematic: indexname * term option -> indexname * term option
  val add_binds: (indexname * string option) list -> context -> context
  val add_binds_i: (indexname * term option) list -> context -> context
  val auto_bind_goal: term list -> context -> context
  val auto_bind_facts: term list -> context -> context
  val match_bind: bool -> (string list * string) list -> context -> context
  val match_bind_i: bool -> (term list * term) list -> context -> context
  val read_propp: context * (string * (string list * string list)) list list
    -> context * (term * (term list * term list)) list list
  val cert_propp: context * (term * (term list * term list)) list list
    -> context * (term * (term list * term list)) list list
  val read_propp_schematic: context * (string * (string list * string list)) list list
    -> context * (term * (term list * term list)) list list
  val cert_propp_schematic: context * (term * (term list * term list)) list list
    -> context * (term * (term list * term list)) list list
  val bind_propp: context * (string * (string list * string list)) list list
    -> context * (term list list * (context -> context))
  val bind_propp_i: context * (term * (term list * term list)) list list
    -> context * (term list list * (context -> context))
  val bind_propp_schematic: context * (string * (string list * string list)) list list
    -> context * (term list list * (context -> context))
  val bind_propp_schematic_i: context * (term * (term list * term list)) list list
    -> context * (term list list * (context -> context))
  val get_thm: context -> thmref -> thm
  val get_thm_closure: context -> thmref -> thm
  val get_thms: context -> thmref -> thm list
  val get_thms_closure: context -> thmref -> thm list
  val valid_thms: context -> string * thm list -> bool
  val lthms_containing: context -> FactIndex.spec -> (string * thm list) list
  val extern_thm: context -> string -> xstring
  val qualified_names: context -> context
  val no_base_names: context -> context
  val custom_accesses: (string list -> string list list) -> context -> context
  val restore_naming: context -> context -> context
  val hide_thms: bool -> string list -> context -> context
  val put_thms: string * thm list option -> context -> context
  val note_thmss:
    ((bstring * context attribute list) * (thmref * context attribute list) list) list ->
      context -> context * (bstring * thm list) list
  val note_thmss_i:
    ((bstring * context attribute list) * (thm list * context attribute list) list) list ->
      context -> context * (bstring * thm list) list
  val export_assume: exporter
  val export_presume: exporter
  val cert_def: context -> term -> string * term
  val export_def: exporter
  val assume: exporter
    -> ((string * context attribute list) * (string * (string list * string list)) list) list
    -> context -> context * (bstring * thm list) list
  val assume_i: exporter
    -> ((string * context attribute list) * (term * (term list * term list)) list) list
    -> context -> context * (bstring * thm list) list
  val add_view: context -> cterm list -> context -> context
  val export_standard_view: cterm list -> context -> context -> thm -> thm
  val read_vars: context * (string list * string option)
    -> context * (string list * typ option)
  val cert_vars: context * (string list * typ option)
    -> context * (string list * typ option)
  val read_vars_liberal: context * (string list * string option)
    -> context * (string list * typ option)
  val cert_vars_liberal: context * (string list * typ option)
    -> context * (string list * typ option)
  val fix: (string list * string option) list -> context -> context
  val fix_i: (string list * typ option) list -> context -> context
  val add_fixes: (string * typ option * Syntax.mixfix option) list -> context -> context
  val add_fixes_liberal: (string * typ option * Syntax.mixfix option) list -> context -> context
  val fix_frees: term list -> context -> context
  val bind_skolem: context -> string list -> term -> term
  val apply_case: RuleCases.T -> context
    -> context * ((indexname * term option) list * (string * term list) list)
  val get_case: context -> string -> string option list -> RuleCases.T
  val add_cases: (string * RuleCases.T option) list -> context -> context
  val verbose: bool ref
  val setmp_verbose: ('a -> 'b) -> 'a -> 'b
  val print_syntax: context -> unit
  val print_binds: context -> unit
  val print_lthms: context -> unit
  val print_cases: context -> unit
  val prems_limit: int ref
  val pretty_asms: context -> Pretty.T list
  val pretty_context: context -> Pretty.T list
end;

structure ProofContext: PROOF_CONTEXT =
struct

(** generic proof contexts **)

type context = Context.proof;
exception CONTEXT = Context.PROOF;

val theory_of = Context.theory_of_proof;
val sign_of = theory_of;

val init = Context.init_proof;



(** Isar proof context information **)

type exporter = bool -> cterm list -> thm -> thm Seq.seq;

datatype ctxt =
  Ctxt of
   {syntax: (Syntax.syntax * Syntax.syntax * (Syntax.syntax -> Syntax.syntax)) *
      string list * string list,                (*global/local syntax with structs and mixfixed*)
    asms:
      ((cterm list * exporter) list *           (*assumes and views: A ==> _*)
        (string * thm list) list) *             (*prems: A |- A *)
      (string * string) list,                   (*fixes: !!x. _*)
    binds: (term * typ) Vartab.table,           (*term bindings*)
    thms: NameSpace.naming *                    (*local thms*)
      thm list NameSpace.table * FactIndex.T,
    cases: (string * RuleCases.T) list,         (*local contexts*)
    defs:
      typ Vartab.table *                        (*type constraints*)
      sort Vartab.table *                       (*default sorts*)
      string list *                             (*used type variables*)
      term list Symtab.table};                  (*type variable occurrences*)

fun make_ctxt (syntax, asms, binds, thms, cases, defs) =
  Ctxt {syntax = syntax, asms = asms, binds = binds, thms = thms, cases = cases, defs = defs};

structure ContextData = ProofDataFun
(struct
  val name = "Isar/context";
  type T = ctxt;
  fun init thy =
    make_ctxt (((Sign.syn_of thy, Sign.syn_of thy, I), [], []), (([], []), []),
      Vartab.empty, (NameSpace.default_naming, NameSpace.empty_table, FactIndex.empty), [],
      (Vartab.empty, Vartab.empty, [], Symtab.empty));
  fun print _ _ = ();
end);

val _ = Context.add_setup [ContextData.init];

fun rep_context ctxt = ContextData.get ctxt |> (fn Ctxt args => args);

fun map_context f = ContextData.map (fn Ctxt {syntax, asms, binds, thms, cases, defs} =>
  make_ctxt (f (syntax, asms, binds, thms, cases, defs)));

val syntax_of = #syntax o rep_context;

val assumptions_of = #1 o #1 o #asms o rep_context;
val prems_of = List.concat o map #2 o #2 o #1 o #asms o rep_context;
val fixes_of = #2 o #asms o rep_context;
val fixed_names_of = map #2 o fixes_of;

val binds_of =  #binds o rep_context;

val thms_of = #thms o rep_context;
val fact_index_of = #3 o thms_of;

val cases_of = #cases o rep_context;

val defaults_of = #defs o rep_context;
val type_occs_of = #4 o defaults_of;

fun is_fixed ctxt x = exists (equal x o #2) (fixes_of ctxt);
fun is_known ctxt x = Vartab.defined (#1 (defaults_of ctxt)) (x, ~1) orelse is_fixed ctxt x;



(** local syntax **)

val fixedN = "\\<^fixed>";
val structN = "\\<^struct>";


(* translation functions *)

fun fixed_tr x = (fixedN ^ x, curry Term.list_comb (Syntax.free x));

fun context_tr' ctxt =
  let
    val (_, structs, mixfixed) = syntax_of ctxt;

    fun tr' (t $ u) = tr' t $ tr' u
      | tr' (Abs (x, T, t)) = Abs (x, T, tr' t)
      | tr' (t as Free (x, T)) =
          let val i = Library.find_index_eq x structs + 1 in
            if i = 0 andalso x mem_string mixfixed then Const (fixedN ^ x, T)
            else if i = 1 andalso not (! show_structs) then
              Syntax.const "_struct" $ Syntax.const "_indexdefault"
            else t
          end
      | tr' a = a;
  in tr' end;


(* add syntax *)

fun mixfix_type mx = replicate (Syntax.mixfix_args mx) TypeInfer.logicT ---> TypeInfer.logicT;

local

fun mixfix x NONE mx = (fixedN ^ x, mixfix_type mx, Syntax.fix_mixfix x mx)
  | mixfix x (SOME T) mx = (fixedN ^ x, T, Syntax.fix_mixfix x mx);

fun prep_mixfix (_, _, NONE) = NONE
  | prep_mixfix (x, opt_T, SOME mx) = SOME (mixfix x opt_T mx);

fun prep_mixfix' (_, _, NONE) = NONE
  | prep_mixfix' (x, _, SOME Syntax.NoSyn) = NONE
  | prep_mixfix' (x, opt_T, _) = SOME (x, mixfix x opt_T (Syntax.literal x));

fun prep_struct (x, _, NONE) = SOME x
  | prep_struct _ = NONE;

fun mk trs = map Syntax.mk_trfun trs;

fun extend_syntax thy extend (global_syn, syn, mk_syn) =
  let
    val thy_syn = Sign.syn_of thy;
    val mk_syn' = extend o mk_syn;
    val (global_syn', syn') =
      if Syntax.eq_syntax (global_syn, thy_syn)
      then (global_syn, extend syn)
      else (thy_syn, mk_syn' thy_syn);    (*potentially expensive*)
  in (global_syn', syn', mk_syn') end;

in

fun add_syntax decls ctxt = ctxt |> map_context (fn (syntax, asms, binds, thms, cases, defs) =>
  let
    val (syns, structs, mixfixed) = syntax;
    val thy = theory_of ctxt;

    val is_logtype = Sign.is_logtype thy;
    val structs' = structs @ List.mapPartial prep_struct decls;
    val mxs = List.mapPartial prep_mixfix decls;
    val (fixed, mxs_output) = Library.split_list (List.mapPartial prep_mixfix' decls);
    val trs = map fixed_tr fixed;

    val extend =
      Syntax.extend_const_gram is_logtype ("", false) mxs_output
      #> Syntax.extend_const_gram is_logtype ("", true) mxs
      #> Syntax.extend_trfuns ([], mk trs, [], []);
    val syns' = extend_syntax thy extend syns;
  in ((syns', structs', fixed @ mixfixed), asms, binds, thms, cases, defs) end);

fun syn_of' thy ctxt =
  let
    val (syns, structs, _) = syntax_of ctxt;
    val (atrs, trs, trs', atrs') = Syntax.struct_trfuns structs;
    val extend = Syntax.extend_trfuns (mk atrs, mk trs, mk trs', mk atrs');
  in #2 (extend_syntax thy extend syns) end;

fun syn_of ctxt = syn_of' (theory_of ctxt) ctxt;

end;

fun transfer thy = add_syntax [] o Context.transfer_proof thy;



(** pretty printing **)

fun pretty_term' thy ctxt t = Sign.pretty_term' (syn_of' thy ctxt) thy (context_tr' ctxt t);
fun pretty_term ctxt t = pretty_term' (theory_of ctxt) ctxt (context_tr' ctxt t);
fun pretty_typ ctxt T = Sign.pretty_typ (theory_of ctxt) T;
fun pretty_sort ctxt S = Sign.pretty_sort (theory_of ctxt) S;
fun pretty_classrel ctxt cs = Sign.pretty_classrel (theory_of ctxt) cs;
fun pretty_arity ctxt ar = Sign.pretty_arity (theory_of ctxt) ar;

fun pp ctxt = Pretty.pp (pretty_term ctxt, pretty_typ ctxt, pretty_sort ctxt,
  pretty_classrel ctxt, pretty_arity ctxt);

val string_of_typ = Pretty.string_of oo pretty_typ;
val string_of_term = Pretty.string_of oo pretty_term;

fun pretty_thm ctxt thm =
  if ! Display.show_hyps then
    Display.pretty_thm_aux (pp ctxt) false thm
  else pretty_term ctxt (Thm.prop_of thm);

fun pretty_thms ctxt [th] = pretty_thm ctxt th
  | pretty_thms ctxt ths = Pretty.blk (0, Pretty.fbreaks (map (pretty_thm ctxt) ths));

fun pretty_fact ctxt ("", ths) = pretty_thms ctxt ths
  | pretty_fact ctxt (a, [th]) =
      Pretty.block [Pretty.str (a ^ ":"), Pretty.brk 1, pretty_thm ctxt th]
  | pretty_fact ctxt (a, ths) =
      Pretty.block (Pretty.fbreaks (Pretty.str (a ^ ":") :: map (pretty_thm ctxt) ths));

fun pretty_proof ctxt prf =
  pretty_term' (ProofSyntax.proof_syntax prf (theory_of ctxt)) ctxt
    (ProofSyntax.term_of_proof prf);

fun pretty_proof_of ctxt full th =
  pretty_proof ctxt (ProofSyntax.proof_of full th);



(** default sorts and types **)

val def_sort = Vartab.lookup o #2 o defaults_of;

fun def_type ctxt pattern xi =
  let val {binds, defs = (types, _, _, _), ...} = rep_context ctxt in
    (case Vartab.lookup types xi of
      NONE =>
        if pattern then NONE
        else Vartab.lookup binds xi |> Option.map (TypeInfer.polymorphicT o #2)
    | some => some)
  end;

fun default_type ctxt x = Vartab.lookup (#1 (defaults_of ctxt)) (x, ~1);
val used_types = #3 o defaults_of;



(** prepare types **)

local

fun read_typ_aux read ctxt s =
  transform_error (read (syn_of ctxt) (theory_of ctxt, def_sort ctxt)) s
    handle ERROR_MESSAGE msg => raise CONTEXT (msg, ctxt);

fun cert_typ_aux cert ctxt raw_T =
  cert (theory_of ctxt) raw_T
    handle TYPE (msg, _, _) => raise CONTEXT (msg, ctxt);

in

val read_typ        = read_typ_aux Sign.read_typ';
val read_typ_syntax = read_typ_aux Sign.read_typ_syntax';
val read_typ_abbrev = read_typ_aux Sign.read_typ_abbrev';
val cert_typ        = cert_typ_aux Sign.certify_typ;
val cert_typ_syntax = cert_typ_aux Sign.certify_typ_syntax;
val cert_typ_abbrev = cert_typ_aux Sign.certify_typ_abbrev;

end;


(* internalize Skolem constants *)

val lookup_skolem = AList.lookup (op =) o fixes_of;
fun get_skolem ctxt x = if_none (lookup_skolem ctxt x) x;

fun no_skolem internal ctxt x =
  if can Syntax.dest_skolem x then
    raise CONTEXT ("Illegal reference to internal Skolem constant: " ^ quote x, ctxt)
  else if not internal andalso can Syntax.dest_internal x then
    raise CONTEXT ("Illegal reference to internal variable: " ^ quote x, ctxt)
  else x;

fun intern_skolem ctxt internal =
  let
    fun intern (t as Free (x, T)) =
          if internal x then t
          else
            (case lookup_skolem ctxt (no_skolem false ctxt x) of
              SOME x' => Free (x', T)
            | NONE => t)
      | intern (t $ u) = intern t $ intern u
      | intern (Abs (x, T, t)) = Abs (x, T, intern t)
      | intern a = a;
  in intern end;


(* externalize Skolem constants -- for printing purposes only *)

fun extern_skolem ctxt =
  let
    val rev_fixes = map Library.swap (fixes_of ctxt);

    fun extern (t as Free (x, T)) =
          (case AList.lookup (op =) rev_fixes x of
            SOME x' => Free (if lookup_skolem ctxt x' = SOME x then x' else NameSpace.hidden x', T)
          | NONE => t)
      | extern (t $ u) = extern t $ extern u
      | extern (Abs (x, T, t)) = Abs (x, T, extern t)
      | extern a = a;
  in extern end


(** prepare terms and propositions **)

(*
  (1) read / certify wrt. theory of context
  (2) intern Skolem constants
  (3) expand term bindings
*)


(* read wrt. theory *)     (*exception ERROR*)

fun read_def_termTs freeze pp syn thy (types, sorts, used) sTs =
  Sign.read_def_terms' pp (Sign.is_logtype thy) syn (thy, types, sorts) used freeze sTs;

fun read_def_termT freeze pp syn thy defs sT =
  apfst hd (read_def_termTs freeze pp syn thy defs [sT]);

fun read_term_thy freeze pp syn thy defs s =
  #1 (read_def_termT freeze pp syn thy defs (s, TypeInfer.logicT));

fun read_prop_thy freeze pp syn thy defs s =
  #1 (read_def_termT freeze pp syn thy defs (s, propT));

fun read_terms_thy freeze pp syn thy defs =
  #1 o read_def_termTs freeze pp syn thy defs o map (rpair TypeInfer.logicT);

fun read_props_thy freeze pp syn thy defs =
  #1 o read_def_termTs freeze pp syn thy defs o map (rpair propT);


(* norm_term *)

(*beta normal form for terms (not eta normal form), chase variables in
  bindings environment (code taken from Pure/envir.ML)*)

fun unifyT ctxt (T, U) =
  let val maxidx = Int.max (Term.maxidx_of_typ T, Term.maxidx_of_typ U)
  in #1 (Sign.typ_unify (theory_of ctxt) (T, U) (Vartab.empty, maxidx)) end;

fun norm_term ctxt schematic =
  let
    (*raised when norm has no effect on a term, to do sharing instead of copying*)
    exception SAME;

    val binds = binds_of ctxt;
    fun norm (t as Var (xi, T)) =
          (case Vartab.lookup binds xi of
            SOME (u, U) =>
              let
                val env = unifyT ctxt (T, U) handle Type.TUNIFY =>
                  raise TYPE ("norm_term: ill-typed variable assignment", [T, U], [t, u]);
                val u' = Envir.subst_TVars env u;
              in norm u' handle SAME => u' end
          | NONE =>
            if schematic then raise SAME
            else raise CONTEXT ("Unbound schematic variable: " ^ Syntax.string_of_vname xi, ctxt))
      | norm (Abs (a, T, body)) =  Abs (a, T, norm body)
      | norm (Abs (_, _, body) $ t) = normh (subst_bound (t, body))
      | norm (f $ t) =
          ((case norm f of
            Abs (_, _, body) => normh (subst_bound (t, body))
          | nf => nf $ (norm t handle SAME => t)) handle SAME => f $ norm t)
      | norm _ =  raise SAME
    and normh t = norm t handle SAME => t
  in normh end;


(* dummy patterns *)

fun prepare_dummies t = #2 (Term.replace_dummy_patterns (1, t));

fun reject_dummies ctxt t = Term.no_dummy_patterns t
  handle TERM _ => raise CONTEXT ("Illegal dummy pattern(s) in term", ctxt);


(* read terms *)

local

fun append_env e1 e2 x = (case e2 x of NONE => e1 x | some => some);

fun gen_read' read app pattern schematic
    ctxt internal more_types more_sorts more_used s =
  let
    val types = append_env (def_type ctxt pattern) more_types;
    val sorts = append_env (def_sort ctxt) more_sorts;
    val used = used_types ctxt @ more_used;
  in
    (transform_error (read (pp ctxt) (syn_of ctxt) (theory_of ctxt) (types, sorts, used)) s
      handle TERM (msg, _) => raise CONTEXT (msg, ctxt)
        | ERROR_MESSAGE msg => raise CONTEXT (msg, ctxt))
    |> app (intern_skolem ctxt internal)
    |> app (if pattern then I else norm_term ctxt schematic)
    |> app (if pattern then prepare_dummies else reject_dummies ctxt)
  end;

fun gen_read read app pattern schematic ctxt =
  gen_read' read app pattern schematic ctxt (K false) (K NONE) (K NONE) [];

in

val read_termTs           = gen_read' (read_def_termTs false) (apfst o map) false false;
val read_termTs_schematic = gen_read' (read_def_termTs false) (apfst o map) false true;

fun read_term_pats T ctxt =
  #1 o gen_read (read_def_termTs false) (apfst o map) true false ctxt o map (rpair T);
val read_prop_pats = read_term_pats propT;

fun read_term_liberal ctxt =
  gen_read' (read_term_thy true) I false false ctxt (K true) (K NONE) (K NONE) [];

val read_term              = gen_read (read_term_thy true) I false false;
val read_prop              = gen_read (read_prop_thy true) I false false;
val read_prop_schematic    = gen_read (read_prop_thy true) I false true;
val read_terms             = gen_read (read_terms_thy true) map false false;
fun read_props schematic   = gen_read (read_props_thy true) map false schematic;

end;


(* certify terms *)

local

fun gen_cert cert pattern schematic ctxt t = t
  |> (if pattern then I else norm_term ctxt schematic)
  |> (fn t' => cert (pp ctxt) (theory_of ctxt) t'
    handle TYPE (msg, _, _) => raise CONTEXT (msg, ctxt)
      | TERM (msg, _) => raise CONTEXT (msg, ctxt));

val certify_term = #1 ooo Sign.certify_term;
val certify_prop = #1 ooo Sign.certify_prop;

in

val cert_term = gen_cert certify_term false false;
val cert_prop = gen_cert certify_prop false false;
val cert_props = map oo gen_cert certify_prop false;

fun cert_term_pats _ = map o gen_cert certify_term true false;
val cert_prop_pats = map o gen_cert certify_prop true false;

end;


(* declare terms *)

local

val ins_types = fold_aterms
  (fn Free (x, T) => Vartab.update ((x, ~1), T)
    | Var v => Vartab.update v
    | _ => I);

val ins_sorts = fold_types (fold_atyps
  (fn TFree (x, S) => Vartab.update ((x, ~1), S)
    | TVar v => Vartab.update v
    | _ => I));

val ins_used = fold_term_types (fn t =>
  fold_atyps (fn TFree (x, _) => insert (op =) x | _ => I));

val ins_occs = fold_term_types (fn t =>
  fold_atyps (fn TFree (x, _) => Symtab.update_multi (x, t) | _ => I));

fun ins_skolem def_ty = fold_rev (fn (x, x') =>
  (case def_ty x' of
    SOME T => Vartab.update ((x, ~1), T)
  | NONE => I));

fun map_defaults f = map_context (fn (syntax, asms, binds, thms, cases, defs) =>
  (syntax, asms, binds, thms, cases, f defs));

in

fun declare_term_syntax t ctxt =
  ctxt
  |> map_defaults (fn (types, sorts, used, occ) => (ins_types t types, sorts, used, occ))
  |> map_defaults (fn (types, sorts, used, occ) => (types, ins_sorts t sorts, used, occ))
  |> map_defaults (fn (types, sorts, used, occ) => (types, sorts, ins_used t used, occ));

fun declare_term t ctxt =
  ctxt
  |> declare_term_syntax t
  |> map_defaults (fn (types, sorts, used, occ) => (types, sorts, used, ins_occs t occ))
  |> map_defaults (fn (types, sorts, used, occ) =>
      (ins_skolem (fn x => Vartab.lookup types (x, ~1)) (fixes_of ctxt) types,
        sorts, used, occ));

end;


(* type and constant names *)

fun read_tyname ctxt c =
  if c mem_string used_types ctxt then
    TFree (c, if_none (def_sort ctxt (c, ~1)) (Sign.defaultS (theory_of ctxt)))
  else Sign.read_tyname (theory_of ctxt) c;

fun read_const ctxt c =
  (case lookup_skolem ctxt c of
    SOME c' => Free (c', dummyT)
  | NONE => Sign.read_const (theory_of ctxt) c);



(** Hindley-Milner polymorphism **)

(* warn_extra_tfrees *)

fun warn_extra_tfrees ctxt1 ctxt2 =
  let
    fun known_tfree a (Type (_, Ts)) = exists (known_tfree a) Ts
      | known_tfree a (TFree (a', _)) = a = a'
      | known_tfree _ _ = false;

    val extras =
      Library.gen_rems Library.eq_fst (pairself (Symtab.dest o type_occs_of) (ctxt1, ctxt2))
      |> map (fn (a, ts) => map (pair a) (List.mapPartial (try (#1 o Term.dest_Free)) ts))
      |> List.concat
      |> List.mapPartial (fn (a, x) =>
          (case def_type ctxt1 false (x, ~1) of NONE => SOME (a, x)
          | SOME T => if known_tfree a T then NONE else SOME (a, x)));
    val tfrees = map #1 extras |> Library.sort_strings |> Library.unique_strings;
    val frees = map #2 extras |> Library.sort_strings |> Library.unique_strings;
  in
    if null extras then ()
    else warning ("Just introduced free type variable(s): " ^ commas tfrees ^ " in " ^
      space_implode " or " frees);
    ctxt2
  end;


(* generalize type variables *)

fun generalize_tfrees inner outer =
  let
    val extra_fixes = fixed_names_of inner \\ fixed_names_of outer;
    fun still_fixed (Free (x, _)) = not (x mem_string extra_fixes)
      | still_fixed _ = false;
    val occs_inner = type_occs_of inner;
    val occs_outer = type_occs_of outer;
    fun add a gen =
      if Symtab.defined occs_outer a orelse
        exists still_fixed (Symtab.lookup_multi occs_inner a)
      then gen else a :: gen;
  in fn tfrees => fold add tfrees [] end;

fun generalize inner outer ts =
  let
    val tfrees = generalize_tfrees inner outer (foldr Term.add_term_tfree_names [] ts);
    fun gen (x, S) = if x mem_string tfrees then TVar ((x, 0), S) else TFree (x, S);
  in map (Term.map_term_types (Term.map_type_tfree gen)) ts end;



(** export theorems **)

fun get_free x (t as Free (y, _)) NONE = if x = y then SOME t else NONE
  | get_free _ _ opt = opt;

fun find_free t x = fold_aterms (get_free x) t NONE;

fun export is_goal inner outer =
  let
    val gen = generalize_tfrees inner outer;
    val fixes = fixed_names_of inner \\ fixed_names_of outer;
    val asms = Library.drop (length (assumptions_of outer), assumptions_of inner);
    val exp_asms = map (fn (cprops, exp) => exp is_goal cprops) asms;
  in
    Tactic.norm_hhf_rule
    #> Seq.EVERY (rev exp_asms)
    #> Seq.map (fn rule =>
      let
        val thy = Thm.theory_of_thm rule;
        val prop = Thm.full_prop_of rule;
        val frees = map (Thm.cterm_of thy) (List.mapPartial (find_free prop) fixes);
        val tfrees = gen (Term.add_term_tfree_names (prop, []));
      in
        rule
        |> Drule.forall_intr_list frees
        |> Tactic.norm_hhf_rule
        |> (#1 o Drule.tvars_intr_list tfrees)
      end)
  end;

(*without varification*)
fun export' is_goal inner outer =
  let
    val asms = Library.drop (length (assumptions_of outer), assumptions_of inner);
    val exp_asms = map (fn (cprops, exp) => exp is_goal cprops) asms;
  in
    Tactic.norm_hhf_plain
    #> Seq.EVERY (rev exp_asms)
    #> Seq.map Tactic.norm_hhf_plain
  end;

fun gen_export exp inner outer =
  let val e = exp false inner outer in
    fn th =>
      (case Seq.pull (e th) of
        SOME (th', _) => th' |> Drule.local_standard
      | NONE => sys_error "Failed to export theorem")
  end;

val export_standard = gen_export export;
val export_plain = gen_export export';



(** bindings **)

(* delete_update_binds *)

local

fun del_bind xi = map_context (fn (syntax, asms, binds, thms, cases, defs) =>
  (syntax, asms, Vartab.delete_safe xi binds, thms, cases, defs));

fun upd_bind ((x, i), t) =
  let
    val T = Term.fastype_of t;
    val t' =
      if null (Term.term_tvars t \\ Term.typ_tvars T) then t
      else Var ((x ^ "_has_extra_type_vars_on_rhs", i), T);
  in
    map_context (fn (syntax, asms, binds, thms, cases, defs) =>
      (syntax, asms, Vartab.update ((x, i), (t', T)) binds, thms, cases, defs))
    o declare_term t'
  end;

fun del_upd_bind (xi, NONE) = del_bind xi
  | del_upd_bind (xi, SOME t) = upd_bind (xi, t);

in

val delete_update_binds = fold del_upd_bind;

end;


(* simult_matches *)

fun simult_matches ctxt [] = []
  | simult_matches ctxt pairs =
      let
        fun fail () = raise CONTEXT ("Pattern match failed!", ctxt);

        val maxidx = fold (fn (t1, t2) => fn i =>
          Int.max (Int.max (Term.maxidx_of_term t1, Term.maxidx_of_term t2), i)) pairs ~1;
        val envs = Unify.smash_unifiers (theory_of ctxt, Envir.empty maxidx,
          map swap pairs);    (*prefer assignment of variables from patterns*)
        val env =
          (case Seq.pull envs of
            NONE => fail ()
          | SOME (env, _) => env);    (*ignore further results*)
        val domain =
          filter_out Term.is_replaced_dummy_pattern (map #1 (Drule.vars_of_terms (map #1 pairs)));
        val _ =    (*may not assign variables from text*)
          if null (map #1 (Envir.alist_of env) inter (map #1 (Drule.vars_of_terms (map #2 pairs))))
          then () else fail ();
        fun norm_bind (xi, (_, t)) =
          if mem_ix (xi, domain) then SOME (xi, Envir.norm_term env t) else NONE;
      in List.mapPartial norm_bind (Envir.alist_of env) end;


(* add_binds(_i) *)

local

fun gen_bind prep (xi as (x, _), raw_t) ctxt =
  ctxt |> delete_update_binds [(xi, Option.map (prep ctxt) raw_t)];

in

fun drop_schematic (b as (xi, SOME t)) = if null (Term.term_vars t) then b else (xi, NONE)
  | drop_schematic b = b;

val add_binds = fold (gen_bind read_term);
val add_binds_i = fold (gen_bind cert_term);

fun auto_bind f ts ctxt = ctxt |> add_binds_i (map drop_schematic (f (theory_of ctxt) ts));
val auto_bind_goal = auto_bind AutoBind.goal;
val auto_bind_facts = auto_bind AutoBind.facts;

end;


(* match_bind(_i) *)

local

fun prep_bind prep_pats (ctxt, (raw_pats, t)) =
  let
    val ctxt' = declare_term t ctxt;
    val pats = prep_pats (fastype_of t) ctxt' raw_pats;
    val binds = simult_matches ctxt' (map (rpair t) pats);
  in (ctxt', binds) end;

fun gen_binds prep_terms prep_pats gen raw_binds ctxt =
  let
    val ts = prep_terms ctxt (map snd raw_binds);
    val (ctxt', binds) =
      apsnd List.concat (foldl_map (prep_bind prep_pats) (ctxt, map fst raw_binds ~~ ts));
    val binds' =
      if gen then map #1 binds ~~ generalize ctxt' ctxt (map #2 binds)
      else binds;
    val binds'' = map (apsnd SOME) binds';
  in
    warn_extra_tfrees ctxt
     (if gen then
        ctxt (*sic!*) |> fold declare_term (map #2 binds') |> add_binds_i binds''
      else ctxt' |> add_binds_i binds'')
  end;

in

val match_bind = gen_binds read_terms read_term_pats;
val match_bind_i = gen_binds (map o cert_term) cert_term_pats;

end;


(* propositions with patterns *)

local

fun prep_propp schematic prep_props prep_pats (context, args) =
  let
    fun prep ((ctxt, prop :: props), (_, (raw_pats1, raw_pats2))) =
          let
            val ctxt' = declare_term prop ctxt;
            val pats = prep_pats ctxt' (raw_pats1 @ raw_pats2);    (*simultaneous type inference!*)
          in ((ctxt', props), (prop, splitAt(length raw_pats1, pats))) end
      | prep _ = sys_error "prep_propp";
    val ((context', _), propp) = foldl_map (foldl_map prep)
        ((context, prep_props schematic context (List.concat (map (map fst) args))), args);
  in (context', propp) end;

fun matches ctxt (prop, (pats1, pats2)) =
  simult_matches ctxt (map (rpair prop) pats1 @ map (rpair (Logic.strip_imp_concl prop)) pats2);

fun gen_bind_propp prepp (ctxt, raw_args) =
  let
    val (ctxt', args) = prepp (ctxt, raw_args);
    val binds = List.concat (List.concat (map (map (matches ctxt')) args));
    val propss = map (map #1) args;

    (*generalize result: context evaluated now, binds added later*)
    val gen = generalize ctxt' ctxt;
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

(* get_thm(s) *)

(*beware of proper order of evaluation!*)
fun retrieve_thms from_thy pick ctxt =
  let
    val thy_ref = Theory.self_ref (theory_of ctxt);
    val (_, (space, tab), _) = thms_of ctxt;
  in
    fn xthmref =>
      let
        val thy = Theory.deref thy_ref;
        val thmref = PureThy.map_name_of_thmref (NameSpace.intern space) xthmref;
        val name = PureThy.name_of_thmref thmref;
      in
        (case Symtab.lookup tab name of
          SOME ths => map (Thm.transfer thy) (PureThy.select_thm thmref ths)
        | NONE => from_thy thy xthmref) |> pick name
      end
  end;

val get_thm = retrieve_thms PureThy.get_thms PureThy.single_thm;
val get_thm_closure = retrieve_thms PureThy.get_thms_closure PureThy.single_thm;
val get_thms = retrieve_thms PureThy.get_thms (K I);
val get_thms_closure = retrieve_thms PureThy.get_thms_closure (K I);


(* valid_thms *)

fun valid_thms ctxt (name, ths) =
  (case try (transform_error (fn () => get_thms ctxt (Name name))) () of
    NONE => false
  | SOME ths' => Thm.eq_thms (ths, ths'));


(* lthms_containing *)

fun lthms_containing ctxt spec =
  FactIndex.find (fact_index_of ctxt) spec
  |> List.filter (valid_thms ctxt)
  |> gen_distinct eq_fst;


(* name space operations *)

val extern_thm = NameSpace.extern o #1 o #2 o thms_of;

fun map_naming f = map_context (fn (syntax, asms, binds,
    (naming, table, index), cases, defs) =>
  (syntax, asms, binds, (f naming, table, index), cases, defs));

val qualified_names = map_naming NameSpace.qualified_names;
val no_base_names = map_naming NameSpace.no_base_names;
val custom_accesses = map_naming o NameSpace.custom_accesses;
val restore_naming = map_naming o K o #1 o thms_of;

fun hide_thms fully names = map_context
  (fn (syntax, asms, binds, (naming, (space, tab), index), cases, defs) =>
    (syntax, asms, binds,
      (naming, (fold (NameSpace.hide fully) names space, tab), index), cases, defs));


(* put_thms *)

fun put_thms ("", _) ctxt = ctxt
  | put_thms (bname, NONE) ctxt = ctxt |> map_context
      (fn (syntax, asms, binds, (naming, (space, tab), index), cases, defs) =>
        let
          val name = NameSpace.full naming bname;
          val tab' = Symtab.delete_safe name tab;
        in (syntax, asms, binds, (naming, (space, tab'), index), cases, defs) end)
  | put_thms (bname, SOME ths) ctxt = ctxt |> map_context
      (fn (syntax, asms, binds, (naming, (space, tab), index), cases, defs) =>
        let
          val name = NameSpace.full naming bname;
          val space' = NameSpace.declare naming name space;
          val tab' = Symtab.update (name, ths) tab;
          val index' = FactIndex.add (is_known ctxt) (name, ths) index;
        in (syntax, asms, binds, (naming, (space', tab'), index'), cases, defs) end);


(* note_thmss *)

local

fun gen_note_thss get (ctxt, ((name, more_attrs), ths_attrs)) =
  let
    fun app (th, attrs) (ct, ths) =
      let val (ct', th') = Thm.applys_attributes ((ct, get ctxt th), attrs @ more_attrs)
      in (ct', th' :: ths) end;
    val (ctxt', rev_thms) = fold app ths_attrs (ctxt, []);
    val thms = List.concat (rev rev_thms);
  in (ctxt' |> put_thms (name, SOME thms), (name, thms)) end;

fun gen_note_thmss get args ctxt =
  foldl_map (gen_note_thss get) (ctxt, args);

in

val note_thmss = gen_note_thmss get_thms;
val note_thmss_i = gen_note_thmss (K I);

val note_thmss_accesses = gen_note_thmss get_thms;
val note_thmss_accesses_i = gen_note_thmss (K I);

end;



(** assumptions **)

(* basic exporters *)

fun export_assume true = Seq.single oo Drule.implies_intr_goals
  | export_assume false = Seq.single oo Drule.implies_intr_list;

fun export_presume _ = export_assume false;


(* defs *)

fun cert_def ctxt eq =
  let
    fun err msg = raise CONTEXT (msg ^
      "\nThe error(s) above occurred in local definition: " ^ string_of_term ctxt eq, ctxt);
    val (lhs, rhs) = Logic.dest_equals (Term.strip_all_body eq)
      handle TERM _ => err "Not a meta-equality (==)";
    val (f, xs) = Term.strip_comb lhs;
    val (c, _) = Term.dest_Free f handle TERM _ =>
      err "Head of lhs must be a free/fixed variable";

    fun is_free (Free (x, _)) = not (is_fixed ctxt x)
      | is_free _ = false;
    val extra_frees = List.filter is_free (term_frees rhs) \\ xs;
  in
    conditional (not (forall (is_Bound orf is_free) xs andalso null (duplicates xs))) (fn () =>
      err "Arguments of lhs must be distinct free/bound variables");
    conditional (f mem Term.term_frees rhs) (fn () =>
      err "Element to be defined occurs on rhs");
    conditional (not (null extra_frees)) (fn () =>
      err ("Extra free variables on rhs: " ^ commas_quote (map (#1 o dest_Free) extra_frees)));
    (c, Term.list_all_free (List.mapPartial (try Term.dest_Free) xs, eq))
  end;

fun head_of_def cprop =
  #1 (Term.strip_comb (#1 (Logic.dest_equals (Term.strip_all_body (Thm.term_of cprop)))))
  |> Thm.cterm_of (Thm.theory_of_cterm cprop);

fun export_def _ cprops thm =
  thm
  |> Drule.implies_intr_list cprops
  |> Drule.forall_intr_list (map head_of_def cprops)
  |> Drule.forall_elim_vars 0
  |> RANGE (replicate (length cprops) (Tactic.rtac Drule.reflexive_thm)) 1;


(* assume *)

local

fun add_assm (ctxt, ((name, attrs), props)) =
  let
    val cprops = map (Thm.cterm_of (theory_of ctxt)) props;
    val asms = map (Tactic.norm_hhf_rule o Thm.assume) cprops;

    val ths = map (fn th => ([th], [])) asms;
    val (ctxt', [(_, thms)]) =
      ctxt
      |> auto_bind_facts props
      |> note_thmss_i [((name, attrs), ths)];
  in (ctxt', (cprops, (name, asms), (name, thms))) end;

fun gen_assms prepp exp args ctxt =
  let
    val (ctxt1, propss) = prepp (ctxt, map snd args);
    val (ctxt2, results) = foldl_map add_assm (ctxt1, map fst args ~~ propss);

    val cprops = List.concat (map #1 results);
    val asmss = map #2 results;
    val thmss = map #3 results;
    val ctxt3 = ctxt2 |> map_context
      (fn (syntax, ((asms_ct, asms_th), fixes), binds, thms, cases, defs) =>
        (syntax, ((asms_ct @ [(cprops, exp)], asms_th @ asmss), fixes), binds, thms,
          cases, defs));
    val ctxt4 = ctxt3 |> put_thms ("prems", SOME (prems_of ctxt3));
  in (warn_extra_tfrees ctxt ctxt4, thmss) end;

in

val assume = gen_assms (apsnd #1 o bind_propp);
val assume_i = gen_assms (apsnd #1 o bind_propp_i);

end;


(* views *)

fun add_view outer view =
  map_context (fn (syntax, ((asms, prems), fixes), binds, thms, cases, defs) =>
    let
      val (asms1, asms2) = splitAt (length (assumptions_of outer), asms);
      val asms' = asms1 @ [(view, export_assume)] @ asms2;
    in (syntax, ((asms', prems), fixes), binds, thms, cases, defs) end);

fun export_standard_view view inner outer =
  export_standard (add_view outer view inner) outer;


(* variables *)

local

fun prep_vars prep_typ internal liberal (ctxt, (xs, raw_T)) =
  let
    fun cond_tvars T =
      if internal then T
      else Type.no_tvars T handle TYPE (msg, _, _) => raise CONTEXT (msg, ctxt);

    val _ = if liberal then () else
      (case List.filter (not o Syntax.is_identifier) (map (no_skolem internal ctxt) xs) of
      [] => () | bads => raise CONTEXT ("Bad variable name(s): " ^ commas_quote bads, ctxt));

    val opt_T = Option.map (cond_tvars o prep_typ ctxt) raw_T;
    val T = if_none opt_T TypeInfer.logicT;
    val ctxt' = ctxt |> fold declare_term_syntax (map (fn x => Free (x, T)) xs);
  in (ctxt', (xs, opt_T)) end;

in

val read_vars         = prep_vars read_typ false false;
val cert_vars         = prep_vars cert_typ true false;
val read_vars_liberal = prep_vars read_typ false true;
val cert_vars_liberal = prep_vars cert_typ true true;

end;


(* fix *)

local

fun map_fixes f =
  map_context (fn (syntax, (assumes, fixes), binds, thms, cases, defs) =>
    (syntax, (assumes, f fixes), binds, thms, cases, defs));

fun err_dups ctxt xs = raise CONTEXT ("Duplicate variable(s): " ^ commas_quote xs, ctxt);

val declare =
  fold declare_term_syntax o
  List.mapPartial (fn (_, NONE) => NONE | (x, SOME T) => SOME (Free (x, T)));

fun add_vars xs Ts ctxt =
  let val xs' = Term.variantlist (map Syntax.skolem xs, map #2 (fixes_of ctxt)) in
    ctxt
    |> declare (xs' ~~ Ts)
    |> map_fixes (fn fixes => (xs ~~ xs') @ fixes)
  end;

fun add_vars_direct xs Ts ctxt =
  ctxt
  |> declare (xs ~~ Ts)
  |> map_fixes (fn fixes =>
    (case xs inter_string map #1 fixes of
      [] => (xs ~~ xs) @ fixes
    | dups => err_dups ctxt dups));


fun gen_fix prep add raw_vars ctxt =
  let
    val (ctxt', varss) = foldl_map prep (ctxt, raw_vars);
    val vars = rev (List.concat (map (fn (xs, T) => map (rpair T) xs) varss));
    val xs = map #1 vars;
    val Ts = map #2 vars;
  in
    (case Library.duplicates xs of [] => () | dups => err_dups ctxt dups);
    ctxt' |> add xs Ts
  end;

fun prep_type (x, NONE, SOME mx) = ([x], SOME (mixfix_type mx))
  | prep_type (x, opt_T, _) = ([x], opt_T);

in

val fix = gen_fix read_vars add_vars;
val fix_i = gen_fix cert_vars add_vars;

fun fix_direct liberal =
  gen_fix (if liberal then cert_vars_liberal else cert_vars) add_vars_direct;

fun add_fixes decls = add_syntax decls o fix_direct false (map prep_type decls);
fun add_fixes_liberal decls = add_syntax decls o fix_direct true (map prep_type decls);

end;

fun fix_frees ts ctxt =
  let
    val frees = fold Term.add_frees ts [];
    fun new (x, T) = if is_fixed ctxt x then NONE else SOME ([x], SOME T);
  in fix_direct false (rev (List.mapPartial new frees)) ctxt end;


(*Note: improper use may result in variable capture / dynamic scoping!*)
fun bind_skolem ctxt xs =
  let
    val ctxt' = ctxt |> fix_i [(xs, NONE)];
    fun bind (t as Free (x, T)) =
          if x mem_string xs then
            (case lookup_skolem ctxt' x of SOME x' => Free (x', T) | NONE => t)
          else t
      | bind (t $ u) = bind t $ bind u
      | bind (Abs (x, T, t)) = Abs (x, T, bind t)
      | bind a = a;
  in bind end;



(** cases **)

fun apply_case ({fixes, assumes, binds}: RuleCases.T) ctxt =
  let
    fun bind (c, (x, T)) = (c |> fix_i [([x], SOME T)], bind_skolem c [x] (Free (x, T)));
    val (ctxt', xs) = foldl_map bind (ctxt, fixes);
    fun app t = Library.foldl Term.betapply (t, xs);
  in (ctxt', (map (apsnd (Option.map app)) binds, map (apsnd (map app)) assumes)) end;

local

fun prep_case ctxt name xs {fixes, assumes, binds} =
  let
    fun replace (opt_x :: xs) ((y, T) :: ys) = (if_none opt_x y, T) :: replace xs ys
      | replace [] ys = ys
      | replace (_ :: _) [] = raise CONTEXT ("Too many parameters for case " ^ quote name, ctxt);
  in
    if null (foldr Term.add_typ_tvars [] (map snd fixes)) andalso
      null (foldr Term.add_term_vars [] (List.concat (map snd assumes))) then
        {fixes = replace xs fixes, assumes = assumes, binds = map drop_schematic binds}
    else raise CONTEXT ("Illegal schematic variable(s) in case " ^ quote name, ctxt)
  end;

fun rem_case name = remove (fn (x: string, (y, _)) => x = y) name;

fun add_case ("", _) cases = cases
  | add_case (name, NONE) cases = rem_case name cases
  | add_case (name, SOME c) cases = (name, c) :: rem_case name cases;

in

fun get_case ctxt name xs =
  (case AList.lookup (op =) (cases_of ctxt) name of
    NONE => raise CONTEXT ("Unknown case: " ^ quote name, ctxt)
  | SOME c => prep_case ctxt name xs c);

fun add_cases xs = map_context (fn (syntax, asms, binds, thms, cases, defs) =>
  (syntax, asms, binds, thms, fold add_case xs cases, defs));

end;



(** print context information **)

val verbose = ref false;
fun verb f x = if ! verbose then f (x ()) else [];
fun verb_single x = verb Library.single x;

fun setmp_verbose f x = Library.setmp verbose true f x;

fun pretty_items prt name items =
  let
    fun prt_itms (name, [x]) = Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1, prt x]
      | prt_itms (name, xs) = Pretty.big_list (name ^ ":") (map prt xs);
  in
    if null items andalso not (! verbose) then []
    else [Pretty.big_list name (map prt_itms items)]
  end;


(* local syntax *)

val print_syntax = Syntax.print_syntax o syn_of;


(* term bindings *)

fun pretty_binds ctxt =
  let
    val binds = binds_of ctxt;
    fun prt_bind (xi, (t, T)) = pretty_term ctxt (Logic.mk_equals (Var (xi, T), t));
  in
    if Vartab.is_empty binds andalso not (! verbose) then []
    else [Pretty.big_list "term bindings:" (map prt_bind (Vartab.dest binds))]
  end;

val print_binds = Pretty.writeln o Pretty.chunks o pretty_binds;


(* local theorems *)

fun pretty_lthms ctxt =
  pretty_items (pretty_thm ctxt) "facts:" (NameSpace.extern_table (#2 (thms_of ctxt)));

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
            List.concat (Library.separate sep (map (Library.single o prt) xs))))];

    fun prt_case (name, (fixes, (lets, asms))) = Pretty.block (Pretty.fbreaks
      (Pretty.str (name ^ ":") ::
        prt_sect "fix" [] (Pretty.str o fst) fixes @
        prt_sect "let" [Pretty.str "and"] prt_let
          (List.mapPartial (fn (xi, SOME t) => SOME (xi, t) | _ => NONE) lets) @
        (if forall (null o #2) asms then []
          else prt_sect "assume" [Pretty.str "and"] prt_asm asms)));

    val cases = cases_of ctxt;
  in
    if null cases andalso not (! verbose) then []
    else [Pretty.big_list "cases:"
      (map (prt_case o apsnd (fn c => (#fixes c, #2 (apply_case c ctxt)))) (rev cases))]
  end;

val print_cases = Pretty.writeln o Pretty.chunks o pretty_cases;


(* core context *)

val prems_limit = ref 10;

fun pretty_asms ctxt =
  let
    val prt_term = pretty_term ctxt;

    (*structures*)
    val (_, structs, _) = syntax_of ctxt;
    val prt_structs = if null structs then []
      else [Pretty.block (Pretty.str "structures:" :: Pretty.brk 1 ::
        Pretty.commas (map Pretty.str structs))];

    (*fixes*)
    fun prt_fix (x, x') =
      if x = x' then Pretty.str x
      else Pretty.block [Pretty.str x, Pretty.str " =", Pretty.brk 1, prt_term (Syntax.free x')];
    val fixes = rev (filter_out
      ((can Syntax.dest_internal o #1) orf (fn (_, x') => x' mem_string structs)) (fixes_of ctxt));
    val prt_fixes = if null fixes then []
      else [Pretty.block (Pretty.str "fixed variables:" :: Pretty.brk 1 ::
        Pretty.commas (map prt_fix fixes))];

    (*prems*)
    val limit = ! prems_limit;
    val prems = prems_of ctxt;
    val len = length prems;
    val prt_prems = if null prems then []
      else [Pretty.big_list "prems:" ((if len <= limit then [] else [Pretty.str "..."]) @
        map (pretty_thm ctxt) (Library.drop (len - limit, prems)))];

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

    val (types, sorts, used, _) = defaults_of ctxt;
  in
    verb_single (K pretty_thy) @
    pretty_asms ctxt @
    verb pretty_binds (K ctxt) @
    verb pretty_lthms (K ctxt) @
    verb pretty_cases (K ctxt) @
    verb_single (fn () => Pretty.big_list "type constraints:" (map prt_defT (Vartab.dest types))) @
    verb_single (fn () => Pretty.big_list "default sorts:" (map prt_defS (Vartab.dest sorts))) @
    verb_single (fn () => Pretty.strs ("used type variable names:" :: used))
  end;

end;
