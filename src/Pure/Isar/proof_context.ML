(*  Title:      Pure/Isar/proof_context.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The key concept of Isar proof contexts: elevates primitive local
reasoning Gamma |- phi to a structured concept, with generic context
elements.
*)

signature PROOF_CONTEXT =
sig
  type context (*= Context.proof*)
  type export
  val theory_of: context -> theory
  val init: theory -> context
  val full_name: context -> bstring -> string
  val consts_of: context -> Consts.T
  val set_syntax_mode: string * bool -> context -> context
  val restore_syntax_mode: context -> context -> context
  val assms_of: context -> term list
  val prems_of: context -> thm list
  val fact_index_of: context -> FactIndex.T
  val transfer: theory -> context -> context
  val map_theory: (theory -> theory) -> context -> context
  val pretty_term: context -> term -> Pretty.T
  val pretty_typ: context -> typ -> Pretty.T
  val pretty_sort: context -> sort -> Pretty.T
  val pretty_classrel: context -> class list -> Pretty.T
  val pretty_arity: context -> arity -> Pretty.T
  val pp: context -> Pretty.pp
  val pretty_thm: context -> thm -> Pretty.T
  val pretty_thms: context -> thm list -> Pretty.T
  val pretty_fact: context -> string * thm list -> Pretty.T
  val pretty_proof: context -> Proofterm.proof -> Pretty.T
  val pretty_proof_of: context -> bool -> thm -> Pretty.T
  val string_of_typ: context -> typ -> string
  val string_of_term: context -> term -> string
  val string_of_thm: context -> thm -> string
  val read_typ: context -> string -> typ
  val read_typ_syntax: context -> string -> typ
  val read_typ_abbrev: context -> string -> typ
  val cert_typ: context -> typ -> typ
  val cert_typ_syntax: context -> typ -> typ
  val cert_typ_abbrev: context -> typ -> typ
  val get_skolem: context -> string -> string
  val revert_skolem: context -> string -> string
  val extern_skolem: context -> term -> term
  val read_termTs: context -> (string -> bool) -> (indexname -> typ option)
    -> (indexname -> sort option) -> string list -> (string * typ) list
    -> term list * (indexname * typ) list
  val read_termTs_schematic: context -> (string -> bool) -> (indexname -> typ option)
    -> (indexname -> sort option) -> string list -> (string * typ) list
    -> term list * (indexname * typ) list
  val read_term_legacy: context -> string -> term
  val read_term: context -> string -> term
  val read_prop: context -> string -> term
  val read_prop_schematic: context -> string -> term
  val read_term_pats: typ -> context -> string list -> term list
  val read_prop_pats: context -> string list -> term list
  val cert_term: context -> term -> term
  val cert_prop: context -> term -> term
  val cert_term_pats: typ -> context -> term list -> term list
  val cert_prop_pats: context -> term list -> term list
  val infer_type: context -> string -> typ
  val inferred_param: string -> context -> (string * typ) * context
  val inferred_fixes: context -> (string * typ) list * context
  val read_tyname: context -> string -> typ
  val read_const: context -> string -> term
  val goal_exports: context -> context -> thm list -> thm list Seq.seq
  val exports: context -> context -> thm list -> thm list Seq.seq
  val export: context -> context -> thm list -> thm list
  val export_standard: context -> context -> thm list -> thm list
  val add_binds: (indexname * string option) list -> context -> context
  val add_binds_i: (indexname * term option) list -> context -> context
  val auto_bind_goal: term list -> context -> context
  val auto_bind_facts: term list -> context -> context
  val match_bind: bool -> (string list * string) list -> context -> term list * context
  val match_bind_i: bool -> (term list * term) list -> context -> term list * context
  val read_propp: context * (string * string list) list list
    -> context * (term * term list) list list
  val cert_propp: context * (term * term list) list list
    -> context * (term * term list) list list
  val read_propp_schematic: context * (string * string list) list list
    -> context * (term * term list) list list
  val cert_propp_schematic: context * (term * term list) list list
    -> context * (term * term list) list list
  val bind_propp: context * (string * string list) list list
    -> context * (term list list * (context -> context))
  val bind_propp_i: context * (term * term list) list list
    -> context * (term list list * (context -> context))
  val bind_propp_schematic: context * (string * string list) list list
    -> context * (term list list * (context -> context))
  val bind_propp_schematic_i: context * (term * term list) list list
    -> context * (term list list * (context -> context))
  val fact_tac: thm list -> int -> tactic
  val some_fact_tac: context -> int -> tactic
  val get_thm: context -> thmref -> thm
  val get_thm_closure: context -> thmref -> thm
  val get_thms: context -> thmref -> thm list
  val get_thms_closure: context -> thmref -> thm list
  val valid_thms: context -> string * thm list -> bool
  val lthms_containing: context -> FactIndex.spec -> (string * thm list) list
  val no_base_names: context -> context
  val qualified_names: context -> context
  val sticky_prefix: string -> context -> context
  val restore_naming: context -> context -> context
  val hide_thms: bool -> string list -> context -> context
  val put_thms: bool -> string * thm list option -> context -> context
  val put_thms_internal: string * thm list option -> context -> context
  val note_thmss:
    ((bstring * attribute list) * (thmref * attribute list) list) list ->
      context -> (bstring * thm list) list * context
  val note_thmss_i:
    ((bstring * attribute list) * (thm list * attribute list) list) list ->
      context -> (bstring * thm list) list * context
  val read_vars: (string * string option * mixfix) list -> context ->
    (string * typ option * mixfix) list * context
  val cert_vars: (string * typ option * mixfix) list -> context ->
    (string * typ option * mixfix) list * context
  val read_vars_legacy: (string * string option * mixfix) list -> context ->
    (string * typ option * mixfix) list * context
  val cert_vars_legacy: (string * typ option * mixfix) list -> context ->
    (string * typ option * mixfix) list * context
  val add_fixes: (string * string option * mixfix) list -> context -> string list * context
  val add_fixes_i: (string * typ option * mixfix) list -> context -> string list * context
  val add_fixes_legacy: (string * typ option * mixfix) list -> context -> string list * context
  val fix_frees: term -> context -> context
  val auto_fixes: context * (term list list * 'a) -> context * (term list list * 'a)
  val bind_fixes: string list -> context -> (term -> term) * context
  val add_assms: export ->
    ((string * attribute list) * (string * string list) list) list ->
    context -> (bstring * thm list) list * context
  val add_assms_i: export ->
    ((string * attribute list) * (term * term list) list) list ->
    context -> (bstring * thm list) list * context
  val assume_export: export
  val presume_export: export
  val add_view: context -> cterm list -> context -> context
  val export_view: cterm list -> context -> context -> thm -> thm
  val add_cases: bool -> (string * RuleCases.T option) list -> context -> context
  val apply_case: RuleCases.T -> context -> (string * term list) list * context
  val get_case: context -> string -> string option list -> RuleCases.T
  val expand_abbrevs: bool -> context -> context
  val add_const_syntax: string * bool -> (string * mixfix) list -> context -> context
  val add_abbrevs: string * bool -> ((bstring * mixfix) * term) list -> context -> context
  val verbose: bool ref
  val setmp_verbose: ('a -> 'b) -> 'a -> 'b
  val print_syntax: context -> unit
  val print_binds: context -> unit
  val print_lthms: context -> unit
  val print_cases: context -> unit
  val prems_limit: int ref
  val pretty_ctxt: context -> Pretty.T list
  val pretty_context: context -> Pretty.T list
  val debug: bool ref
  val pprint_context: context -> pprint_args -> unit
end;

structure ProofContext: PROOF_CONTEXT =
struct

type context = Context.proof;

val theory_of = Context.theory_of_proof;
val tsig_of = Sign.tsig_of o theory_of;

val init = Context.init_proof;



(** Isar proof context information **)

type export = bool -> cterm list -> thm -> thm Seq.seq;

datatype ctxt =
  Ctxt of
   {naming: NameSpace.naming,                     (*local naming conventions*)
    syntax: LocalSyntax.T,                        (*local syntax*)
    consts: Consts.T * Consts.T,                  (*global/local consts*)
    assms:
      ((cterm list * export) list *               (*assumes and views: A ==> _*)
        (string * thm list) list),                (*prems: A |- A*)
    thms: thm list NameSpace.table * FactIndex.T, (*local thms*)
    cases: (string * (RuleCases.T * bool)) list}; (*local contexts*)

fun make_ctxt (naming, syntax, consts, assms, thms, cases) =
  Ctxt {naming = naming, syntax = syntax, consts = consts, assms = assms,
    thms = thms, cases = cases};

val local_naming = NameSpace.default_naming |> NameSpace.add_path "local";

structure ContextData = ProofDataFun
(
  val name = "Isar/context";
  type T = ctxt;
  fun init thy =
    make_ctxt (local_naming, LocalSyntax.init thy,
      (Sign.consts_of thy, Sign.consts_of thy), ([], []),
      (NameSpace.empty_table, FactIndex.empty), []);
  fun print _ _ = ();
);

val _ = Context.add_setup ContextData.init;

fun rep_context ctxt = ContextData.get ctxt |> (fn Ctxt args => args);

fun map_context f =
  ContextData.map (fn Ctxt {naming, syntax, consts, assms, thms, cases} =>
    make_ctxt (f (naming, syntax, consts, assms, thms, cases)));

fun map_naming f =
  map_context (fn (naming, syntax, consts, assms, thms, cases) =>
    (f naming, syntax, consts, assms, thms, cases));

fun map_syntax f =
  map_context (fn (naming, syntax, consts, assms, thms, cases) =>
    (naming, f syntax, consts, assms, thms, cases));

fun map_consts f =
  map_context (fn (naming, syntax, consts, assms, thms, cases) =>
    (naming, syntax, f consts, assms, thms, cases));

fun map_assms f =
  map_context (fn (naming, syntax, consts, assms, thms, cases) =>
    (naming, syntax, consts, f assms, thms, cases));

fun map_thms f =
  map_context (fn (naming, syntax, consts, assms, thms, cases) =>
    (naming, syntax, consts, assms, f thms, cases));

fun map_cases f =
  map_context (fn (naming, syntax, consts, assms, thms, cases) =>
    (naming, syntax, consts, assms, thms, f cases));

val naming_of = #naming o rep_context;
val full_name = NameSpace.full o naming_of;

val syntax_of = #syntax o rep_context;
val syn_of = LocalSyntax.syn_of o syntax_of;
val set_syntax_mode = map_syntax o LocalSyntax.set_mode;
val restore_syntax_mode = map_syntax o LocalSyntax.restore_mode o syntax_of;

val consts_of = #2 o #consts o rep_context;

val assumptions_of = #1 o #assms o rep_context;
val assms_of = map Thm.term_of o maps #1 o assumptions_of;
val prems_of = maps #2 o #2 o #assms o rep_context;

val thms_of = #thms o rep_context;
val fact_index_of = #2 o thms_of;

val cases_of = #cases o rep_context;


(* transfer *)

fun transfer_syntax thy =
  map_syntax (LocalSyntax.rebuild thy) #>
  map_consts (fn consts as (global_consts, local_consts) =>
    let val thy_consts = Sign.consts_of thy in
      if Consts.eq_consts (thy_consts, global_consts) then consts
      else (thy_consts, Consts.merge (thy_consts, local_consts))
    end);

fun transfer thy = Context.transfer_proof thy #> transfer_syntax thy;

fun map_theory f ctxt = transfer (f (theory_of ctxt)) ctxt;



(** pretty printing **)

local

fun rewrite_term thy rews t =
  if can Term.type_of t then Pattern.rewrite_term thy rews [] t
  else (warning "Printing ill-typed term -- cannot expand abbreviations"; t);

fun pretty_term' abbrevs ctxt t =
  let
    val thy = theory_of ctxt;
    val syntax = syntax_of ctxt;
    val consts = consts_of ctxt;
    val t' = t
      |> K abbrevs ? rewrite_term thy (Consts.abbrevs_of consts (! print_mode @ [""]))
      |> Sign.extern_term (Consts.extern_early consts) thy
      |> LocalSyntax.extern_term syntax;
  in
    Sign.pretty_term' (Context.Proof ctxt) (LocalSyntax.syn_of syntax) (Consts.extern consts) t'
  end;

in

val pretty_term = pretty_term' true;
val pretty_term_no_abbrevs = pretty_term' false;

end;

fun pretty_typ ctxt T = Sign.pretty_typ (theory_of ctxt) T;
fun pretty_sort ctxt S = Sign.pretty_sort (theory_of ctxt) S;
fun pretty_classrel ctxt cs = Sign.pretty_classrel (theory_of ctxt) cs;
fun pretty_arity ctxt ar = Sign.pretty_arity (theory_of ctxt) ar;

fun pp ctxt = Pretty.pp (pretty_term ctxt, pretty_typ ctxt, pretty_sort ctxt,
  pretty_classrel ctxt, pretty_arity ctxt);

fun pretty_thm ctxt th =
  Display.pretty_thm_aux (pp ctxt) false true (assms_of ctxt) th;

fun pretty_thms ctxt [th] = pretty_thm ctxt th
  | pretty_thms ctxt ths = Pretty.blk (0, Pretty.fbreaks (map (pretty_thm ctxt) ths));

fun pretty_fact ctxt ("", ths) = pretty_thms ctxt ths
  | pretty_fact ctxt (a, [th]) =
      Pretty.block [Pretty.str (a ^ ":"), Pretty.brk 1, pretty_thm ctxt th]
  | pretty_fact ctxt (a, ths) =
      Pretty.block (Pretty.fbreaks (Pretty.str (a ^ ":") :: map (pretty_thm ctxt) ths));

fun pretty_proof ctxt prf =
  pretty_term_no_abbrevs (ctxt |> transfer_syntax (ProofSyntax.proof_syntax prf (theory_of ctxt)))
    (ProofSyntax.term_of_proof prf);

fun pretty_proof_of ctxt full th =
  pretty_proof ctxt (ProofSyntax.proof_of full th);

val string_of_typ = Pretty.string_of oo pretty_typ;
val string_of_term = Pretty.string_of oo pretty_term;
val string_of_thm = Pretty.string_of oo pretty_thm;



(** prepare types **)

local

fun read_typ_aux read ctxt s =
  read (syn_of ctxt) (Context.Proof ctxt) (Variable.def_sort ctxt) s;

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
  if can Term.dest_skolem x then
    error ("Illegal reference to internal Skolem constant: " ^ quote x)
  else if not internal andalso can Term.dest_internal x then
    error ("Illegal reference to internal variable: " ^ quote x)
  else x;

fun intern_skolem ctxt internal =
  let
    fun intern (t as Free (x, T)) =
          if internal x then t
          else
            (case lookup_skolem ctxt (no_skolem false x) of
              SOME x' => Free (x', T)
            | NONE => t)
      | intern (t $ u) = intern t $ intern u
      | intern (Abs (x, T, t)) = Abs (x, T, intern t)
      | intern a = a;
  in intern end;


(* externalize Skolem constants -- approximation only! *)

fun rev_skolem ctxt =
  let val rev_fixes = map Library.swap (Variable.fixes_of ctxt)
  in AList.lookup (op =) rev_fixes end;

fun revert_skolem ctxt x =
  (case rev_skolem ctxt x of
    SOME x' => x'
  | NONE => perhaps (try Term.dest_skolem) x);

fun extern_skolem ctxt =
  let
    val revert = rev_skolem ctxt;
    fun extern (t as Free (x, T)) =
        (case revert x of
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

fun read_def_termTs freeze pp syn ctxt (types, sorts, used) sTs =
  Sign.read_def_terms' pp (Sign.is_logtype (theory_of ctxt)) syn (consts_of ctxt)
    (Context.Proof ctxt) (types, sorts) used freeze sTs;

fun read_def_termT freeze pp syn ctxt defaults sT =
  apfst hd (read_def_termTs freeze pp syn ctxt defaults [sT]);

fun read_term_thy freeze pp syn thy defaults s =
  #1 (read_def_termT freeze pp syn thy defaults (s, TypeInfer.logicT));

fun read_prop_thy freeze pp syn thy defaults s =
  #1 (read_def_termT freeze pp syn thy defaults (s, propT));

fun read_terms_thy freeze pp syn thy defaults =
  #1 o read_def_termTs freeze pp syn thy defaults o map (rpair TypeInfer.logicT);

fun read_props_thy freeze pp syn thy defaults =
  #1 o read_def_termTs freeze pp syn thy defaults o map (rpair propT);


(* local abbreviations *)

fun certify_consts ctxt =
  Consts.certify (pp ctxt) (tsig_of ctxt) (consts_of ctxt);

fun reject_schematic (Var (xi, _)) =
      error ("Unbound schematic variable: " ^ Syntax.string_of_vname xi)
  | reject_schematic (Abs (_, _, t)) = reject_schematic t
  | reject_schematic (t $ u) = (reject_schematic t; reject_schematic u)
  | reject_schematic _ = ();

fun expand_binds ctxt schematic =
  Variable.expand_binds ctxt #> (if schematic then I else tap reject_schematic);


(* dummy patterns *)

val prepare_dummies =
  let val next = ref 1 in
    fn t =>
      let val (i, u) = Term.replace_dummy_patterns (! next, t)
      in next := i; u end
  end;

fun reject_dummies t = Term.no_dummy_patterns t
  handle TERM _ => error "Illegal dummy pattern(s) in term";


(* read terms *)

local

fun append_env e1 e2 x = (case e2 x of NONE => e1 x | some => some);

fun gen_read' read app pattern schematic
    ctxt internal more_types more_sorts more_used s =
  let
    val types = append_env (Variable.def_type ctxt pattern) more_types;
    val sorts = append_env (Variable.def_sort ctxt) more_sorts;
    val used = Variable.used_types ctxt @ more_used;
  in
    (read (pp ctxt) (syn_of ctxt) ctxt (types, sorts, used) s
      handle TERM (msg, _) => error msg)
    |> app (intern_skolem ctxt internal)
    |> app (certify_consts ctxt)
    |> app (if pattern then I else expand_binds ctxt schematic)
    |> app (if pattern then prepare_dummies else reject_dummies)
  end;

fun gen_read read app pattern schematic ctxt =
  gen_read' read app pattern schematic ctxt (K false) (K NONE) (K NONE) [];

in

val read_termTs           = gen_read' (read_def_termTs false) (apfst o map) false false;
val read_termTs_schematic = gen_read' (read_def_termTs false) (apfst o map) false true;

fun read_term_pats T ctxt =
  #1 o gen_read (read_def_termTs false) (apfst o map) true false ctxt o map (rpair T);
val read_prop_pats = read_term_pats propT;

fun read_term_legacy ctxt =
  gen_read' (read_term_thy true) I false false ctxt (K true) (K NONE) (K NONE) [];

val read_term            = gen_read (read_term_thy true) I false false;
val read_prop            = gen_read (read_prop_thy true) I false false;
val read_prop_schematic  = gen_read (read_prop_thy true) I false true;
val read_terms           = gen_read (read_terms_thy true) map false false;
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
val cert_prop = gen_cert true false false;
val cert_props = map oo gen_cert true false;

fun cert_term_pats _ = map o gen_cert false true false;
val cert_prop_pats = map o gen_cert true true false;

end;


(* inferred types of parameters *)

fun infer_type ctxt x =
  (case try (fn () =>
      Sign.infer_types (pp ctxt) (theory_of ctxt) (consts_of ctxt) (Variable.def_type ctxt false)
        (Variable.def_sort ctxt) (Variable.used_types ctxt) true
        ([Free (x, dummyT)], TypeInfer.logicT)) () of
    SOME (Free (_, T), _) => T
  | _ => error ("Failed to infer type of fixed variable " ^ quote x));

fun inferred_param x ctxt =
  let val T = infer_type ctxt x
  in ((x, T), ctxt |> Variable.declare_syntax (Free (x, T))) end;

fun inferred_fixes ctxt =
  fold_map inferred_param (rev (Variable.fixed_names_of ctxt)) ctxt;


(* type and constant names *)

fun read_tyname ctxt c =
  if member (op =) (Variable.used_types ctxt) c then
    TFree (c, the_default (Sign.defaultS (theory_of ctxt)) (Variable.def_sort ctxt (c, ~1)))
  else Sign.read_tyname (theory_of ctxt) c;

fun read_const ctxt c =
  (case lookup_skolem ctxt c of
    SOME c' => Free (c', dummyT)
  | NONE => Consts.read_const (consts_of ctxt) c);



(** export theorems **)

fun common_exports is_goal inner outer =
  let
    val asms = Library.drop (length (assumptions_of outer), assumptions_of inner);
    val exp_asms = rev (map (fn (cprops, exp) => exp is_goal cprops) asms);
  in
    map Goal.norm_hhf_protect
    #> Seq.map_list (Seq.EVERY exp_asms)
    #> Seq.map (Variable.export inner outer)
    #> Seq.map (map Goal.norm_hhf_protect)
  end;

val goal_exports = common_exports true;
val exports = common_exports false;

fun export inner outer ths =
  (case Seq.pull (common_exports false inner outer ths) of
    SOME (ths', _) => ths'
  | NONE => raise THM ("Failed to export theorems", 0, ths));

fun export_standard inner outer =
  export inner outer #> map Drule.local_standard;



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
val match_bind_i = gen_binds (map o cert_term) cert_term_pats;

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

fun fact_tac facts = Tactic.norm_hhf_tac THEN' comp_incr_tac facts;

fun some_fact_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    val index = fact_index_of ctxt;
    val facts = FactIndex.could_unify index (Term.strip_all_body goal);
  in fact_tac facts i end);


(* get_thm(s) *)

fun retrieve_thms _ pick ctxt (Fact s) =
      let
        val thy = theory_of ctxt;
        val th = Goal.prove thy [] [] (read_prop ctxt s) (K (ALLGOALS (some_fact_tac ctxt)))
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
  |> map ((not o valid_thms ctxt) ? apfst (fn name =>
    NameSpace.hidden (if name = "" then "unnamed" else name)));


(* name space operations *)

val no_base_names   = map_naming NameSpace.no_base_names;
val qualified_names = map_naming NameSpace.qualified_names;
val sticky_prefix   = map_naming o NameSpace.sticky_prefix;
val restore_naming  = map_naming o K o naming_of;

fun hide_thms fully names = map_thms (fn ((space, tab), index) =>
  ((fold (NameSpace.hide fully) names space, tab), index));


(* put_thms *)

fun put_thms _ ("", NONE) ctxt = ctxt
  | put_thms do_index ("", SOME ths) ctxt = ctxt |> map_thms (fn (facts, index) =>
      let
        val index' = FactIndex.add_local do_index (Variable.is_declared ctxt) ("", ths) index;
      in (facts, index') end)
  | put_thms _ (bname, NONE) ctxt = ctxt |> map_thms (fn ((space, tab), index) =>
      let
        val name = full_name ctxt bname;
        val tab' = Symtab.delete_safe name tab;
      in ((space, tab'), index) end)
  | put_thms do_index (bname, SOME ths) ctxt = ctxt |> map_thms (fn ((space, tab), index) =>
      let
        val name = full_name ctxt bname;
        val space' = NameSpace.declare (naming_of ctxt) name space;
        val tab' = Symtab.update (name, ths) tab;
        val index' = FactIndex.add_local do_index (Variable.is_declared ctxt) (name, ths) index;
      in ((space', tab'), index') end);

fun put_thms_internal thms ctxt =
  ctxt |> map_naming (K local_naming) |> put_thms false thms |> restore_naming ctxt;


(* note_thmss *)

local

fun gen_note_thmss get = fold_map (fn ((name, more_attrs), ths_attrs) => fn ctxt =>
  let
    fun app (th, attrs) (ct, ths) =
      let val (ct', th') = foldl_map (Thm.proof_attributes (attrs @ more_attrs)) (ct, get ctxt th)
      in (ct', th' :: ths) end;
    val (ctxt', rev_thms) = fold app ths_attrs (ctxt, []);
    val thms = flat (rev rev_thms);
  in ((name, thms), ctxt' |> put_thms true (name, SOME thms)) end);

in

val note_thmss = gen_note_thmss get_thms;
val note_thmss_i = gen_note_thmss (K I);

val note_thmss_accesses = gen_note_thmss get_thms;
val note_thmss_accesses_i = gen_note_thmss (K I);

end;



(** parameters **)

(* variables *)

fun declare_var (x, opt_T, mx) ctxt =
  let val T = (case opt_T of SOME T => T | NONE => TypeInfer.mixfixT mx)
  in ((x, T, mx), ctxt |> Variable.declare_syntax (Free (x, T))) end;

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

fun add_const_syntax prmode args ctxt =
  ctxt |> map_syntax
    (LocalSyntax.add_modesyntax (theory_of ctxt) prmode
      (map (pair false o Consts.syntax (consts_of ctxt)) args));

fun context_const_ast_tr context [Syntax.Variable c] =
      let
        val consts = Context.cases Sign.consts_of consts_of context;
        val c' = Consts.intern consts c;
        val _ = Consts.constraint consts c' handle TYPE (msg, _, _) => error msg;
      in Syntax.Constant (Syntax.constN ^ c') end
  | context_const_ast_tr _ asts = raise Syntax.AST ("const_ast_tr", asts);

val _ = Context.add_setup
 (Sign.add_syntax
   [("_context_const", "id => 'a", Delimfix "CONST _"),
    ("_context_const", "longid => 'a", Delimfix "CONST _")] #>
  Sign.add_advanced_trfuns ([("_context_const", context_const_ast_tr)], [], [], []));


(* abbreviations *)

val expand_abbrevs = map_consts o apsnd o Consts.expand_abbrevs;

fun add_abbrevs prmode = fold (fn ((raw_c, raw_mx), raw_t) => fn ctxt =>
  let
    val ([(c, _, mx)], _) = cert_vars [(raw_c, NONE, raw_mx)] ctxt;
    val c' = Syntax.constN ^ full_name ctxt c;
    val [t] = Variable.polymorphic ctxt [cert_term (ctxt |> expand_abbrevs false) raw_t];
    val T = Term.fastype_of t;
    val _ =
      if null (Variable.hidden_polymorphism t T) then ()
      else error ("Extra type variables on rhs of abbreviation: " ^ quote c);
  in
    ctxt
    |> Variable.declare_term t
    |> map_consts (apsnd
      (Consts.abbreviate (pp ctxt) (tsig_of ctxt) (naming_of ctxt) (#1 prmode) ((c, t), true)))
    |> map_syntax (LocalSyntax.add_modesyntax (theory_of ctxt) prmode [(false, (c', T, mx))])
  end);


(* fixes *)

local

fun prep_mixfix (x, T, mx) =
  if mx <> NoSyn andalso mx <> Structure andalso
      (can Term.dest_internal x orelse can Term.dest_skolem x) then
    error ("Illegal mixfix syntax for internal/skolem constant " ^ quote x)
  else (true, (x, T, mx));

fun no_dups _ [] = ()
  | no_dups ctxt dups = error ("Duplicate fixed variable(s): " ^ commas_quote dups);

fun gen_fixes prep raw_vars ctxt =
  let
    val (vars, ctxt') = prep raw_vars ctxt;
    val (xs', ctxt'') = Variable.add_fixes (map #1 vars) ctxt';
  in
    ctxt''
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

fun fix_frees t ctxt =
  let
    fun add (Free (x, T)) =
          if Variable.is_fixed ctxt x then I else insert (op =) (x, SOME T, NoSyn)
      | add _ = I;
    val fixes = rev (fold_aterms add t []);
  in
    ctxt
    |> Variable.declare_term t
    |> Variable.set_body false
    |> (snd o add_fixes_i fixes)
    |> Variable.restore_body ctxt
  end;

fun auto_fixes (arg as (ctxt, (propss, x))) =
  if Variable.is_body ctxt then arg
  else ((fold o fold) fix_frees propss ctxt, (propss, x));

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

(* generic assms *)

local

fun gen_assm ((name, attrs), props) ctxt =
  let
    val cprops = map (Thm.cterm_of (theory_of ctxt)) props;
    val asms = map (Goal.norm_hhf o Thm.assume) cprops;

    val ths = map (fn th => ([th], [])) asms;
    val ([(_, thms)], ctxt') =
      ctxt
      |> auto_bind_facts props
      |> note_thmss_i [((name, attrs), ths)];
  in ((cprops, (name, asms), (name, thms)), ctxt') end;

fun gen_assms prepp exp args ctxt =
  let
    val (propss, ctxt1) = swap (prepp (ctxt, map snd args));
    val (results, ctxt2) = fold_map gen_assm (map fst args ~~ propss) ctxt1;

    val new_asms = maps #1 results;
    val new_prems = map #2 results;
    val ctxt3 = ctxt2
      |> map_assms (fn (asms, prems) => (asms @ [(new_asms, exp)], prems @ new_prems))
    val ctxt4 = ctxt3
      |> put_thms_internal (AutoBind.premsN, SOME (prems_of ctxt3));
  in (map #3 results, tap (Variable.warn_extra_tfrees ctxt) ctxt4) end;

in

val add_assms = gen_assms (apsnd #1 o bind_propp);
val add_assms_i = gen_assms (apsnd #1 o bind_propp_i);

end;


(* basic assumptions *)

(*
    [A]
     :
     B
  --------
  #A ==> B
*)
fun assume_export true = Seq.single oo Drule.implies_intr_protected
  | assume_export false = Seq.single oo Drule.implies_intr_list;

(*
    [A]
     :
     B
  -------
  A ==> B
*)
fun presume_export _ = assume_export false;


(* additional views *)

fun add_view outer view = map_assms (fn (asms, prems) =>
  let
    val (asms1, asms2) = chop (length (assumptions_of outer)) asms;
    val asms' = asms1 @ [(view, assume_export)] @ asms2;
  in (asms', prems) end);

fun export_view view inner outer = singleton (export_standard (add_view outer view inner) outer);



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
  in (t, ctxt' |> Variable.declare_syntax t) end;

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

val verbose = ref false;
fun verb f x = if ! verbose then f (x ()) else [];

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


(* local consts *)

fun pretty_consts ctxt =
  let
    val ((_, globals), (space, consts)) =
      pairself (#constants o Consts.dest) (#consts (rep_context ctxt));
    fun local_abbrev (_, (_, NONE)) = I
      | local_abbrev (c, (T, SOME t)) =
          if Symtab.defined globals c then I else cons (c, Logic.mk_equals (Const (c, T), t));
    val abbrevs = NameSpace.extern_table (space, Symtab.make (Symtab.fold local_abbrev consts []));
  in
    if null abbrevs andalso not (! verbose) then []
    else [Pretty.big_list "abbreviations:" (map (pretty_term_no_abbrevs ctxt o #2) abbrevs)]
  end;


(* term bindings *)

fun pretty_binds ctxt =
  let
    val binds = Variable.binds_of ctxt;
    fun prt_bind (xi, (T, t)) = pretty_term_no_abbrevs ctxt (Logic.mk_equals (Var (xi, T), t));
  in
    if Vartab.is_empty binds andalso not (! verbose) then []
    else [Pretty.big_list "term bindings:" (map prt_bind (Vartab.dest binds))]
  end;

val print_binds = Pretty.writeln o Pretty.chunks o pretty_binds;


(* local theorems *)

fun pretty_lthms ctxt =
  pretty_items (pretty_thm ctxt) "facts:" (NameSpace.extern_table (#1 (thms_of ctxt)));

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

val prems_limit = ref 10;

fun pretty_ctxt ctxt =
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
      rev (filter_out ((can Term.dest_internal orf member (op =) structs) o #1)
        (Variable.fixes_of ctxt));
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

    val (types, sorts, used, _) = Variable.defaults_of ctxt;
  in
    verb single (K pretty_thy) @
    pretty_ctxt ctxt @
    verb pretty_consts (K ctxt) @
    verb pretty_binds (K ctxt) @
    verb pretty_lthms (K ctxt) @
    verb pretty_cases (K ctxt) @
    verb single (fn () => Pretty.big_list "type constraints:" (map prt_defT (Vartab.dest types))) @
    verb single (fn () => Pretty.big_list "default sorts:" (map prt_defS (Vartab.dest sorts))) @
    verb single (fn () => Pretty.strs ("used type variable names:" :: rev used))
  end;


(* toplevel pretty printing *)

val debug = ref false;

fun pprint_context ctxt = Pretty.pprint
 (if ! debug then Pretty.quote (Pretty.big_list "proof context:" (pretty_context ctxt))
  else Pretty.str "<context>");

end;
