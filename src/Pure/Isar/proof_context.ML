(*  Title:      Pure/Isar/proof_context.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Proof context information.
*)

signature PROOF_CONTEXT =
sig
  type context
  type exporter
  exception CONTEXT of string * context
  val theory_of: context -> theory
  val sign_of: context -> Sign.sg
  val syntax_of: context -> Syntax.syntax * string list * string list
  val fixed_names_of: context -> string list
  val assumptions_of: context -> (cterm list * exporter) list
  val prems_of: context -> thm list
  val print_proof_data: theory -> unit
  val init: theory -> context
  val is_fixed: context -> string -> bool
  val read_typ: context -> string -> typ
  val read_typ_no_norm: context -> string -> typ
  val cert_typ: context -> typ -> typ
  val cert_typ_no_norm: context -> typ -> typ
  val get_skolem: context -> string -> string
  val intern_skolem: context -> term -> term
  val extern_skolem: context -> term -> term
  val read_termTs: context -> (string * typ) list -> term list * (indexname * typ) list
  val read_term: context -> string -> term
  val read_prop: context -> string -> term
  val read_prop_schematic: context -> string -> term
  val read_terms: context -> string list -> term list
  val read_termT_pats: context -> (string * typ) list -> term list
  val read_term_pats: typ -> context -> string list -> term list
  val read_prop_pats: context -> string list -> term list
  val cert_term: context -> term -> term
  val cert_prop: context -> term -> term
  val cert_term_pats: typ -> context -> term list -> term list
  val cert_prop_pats: context -> term list -> term list
  val declare_term: term -> context -> context
  val declare_terms: term list -> context -> context
  val warn_extra_tfrees: context -> context -> context
  val generalizeT: context -> context -> typ -> typ
  val generalize: context -> context -> term -> term
  val find_free: term -> string -> term option
  val export: bool -> context -> context -> thm -> thm Seq.seq
  val drop_schematic: indexname * term option -> indexname * term option
  val add_binds: (indexname * string option) list -> context -> context
  val add_binds_i: (indexname * term option) list -> context -> context
  val auto_bind_goal: term -> context -> context
  val auto_bind_facts: string -> term list -> context -> context
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
  val get_thm: context -> string -> thm
  val get_thm_closure: context -> string -> thm
  val get_thms: context -> string -> thm list
  val get_thms_closure: context -> string -> thm list
  val put_thm: string * thm -> context -> context
  val put_thms: string * thm list -> context -> context
  val put_thmss: (string * thm list) list -> context -> context
  val reset_thms: string -> context -> context
  val have_thmss:
    ((string * context attribute list) * (thm list * context attribute list) list) list ->
      context -> context * (string * thm list) list
  val export_assume: exporter
  val export_presume: exporter
  val cert_def: context -> term -> string * term
  val export_def: exporter
  val assume: exporter
    -> ((string * context attribute list) * (string * (string list * string list)) list) list
    -> context -> context * (string * thm list) list
  val assume_i: exporter
    -> ((string * context attribute list) * (term * (term list * term list)) list) list
    -> context -> context * (string * thm list) list
  val read_vars: context * (string list * string option) -> context * (string list * typ option)
  val cert_vars: context * (string list * typ option) -> context * (string list * typ option)
  val fix: (string list * string option) list -> context -> context
  val fix_i: (string list * typ option) list -> context -> context
  val fix_direct: (string list * typ option) list -> context -> context
  val fix_frees: term list -> context -> context
  val bind_skolem: context -> string list -> term -> term
  val get_case: context -> string -> string option list -> RuleCases.T
  val add_cases: (string * RuleCases.T) list -> context -> context
  val apply_case: RuleCases.T -> context -> context * ((indexname * term option) list * term list)
  val show_hyps: bool ref
  val add_syntax: (string * typ option * mixfix option) list -> context -> context
  val pretty_term: context -> term -> Pretty.T
  val pretty_typ: context -> typ -> Pretty.T
  val pretty_sort: context -> sort -> Pretty.T
  val pretty_thm: context -> thm -> Pretty.T
  val pretty_thms: context -> thm list -> Pretty.T
  val string_of_term: context -> term -> string
  val verbose: bool ref
  val setmp_verbose: ('a -> 'b) -> 'a -> 'b
  val print_syntax: context -> unit
  val print_binds: context -> unit
  val print_lthms: context -> unit
  val print_cases: context -> unit
  val prems_limit: int ref
  val pretty_asms: context -> Pretty.T list
  val pretty_context: context -> Pretty.T list
  val setup: (theory -> theory) list
end;

signature PRIVATE_PROOF_CONTEXT =
sig
  include PROOF_CONTEXT
  val init_data: Object.kind -> (theory -> Object.T) * (context -> Object.T -> unit)
    -> theory -> theory
  val print_data: Object.kind -> context -> unit
  val get_data: Object.kind -> (Object.T -> 'a) -> context -> 'a
  val put_data: Object.kind -> ('a -> Object.T) -> 'a -> context -> context
end;

structure ProofContext: PRIVATE_PROOF_CONTEXT =
struct


(** datatype context **)

type exporter = bool -> cterm list -> thm -> thm Seq.seq;

datatype context =
  Context of
   {thy: theory,                                           (*current theory*)
    syntax: Syntax.syntax * string list * string list,     (*syntax with structs and mixfixed*)
    data: Object.T Symtab.table,                           (*user data*)
    asms:
      ((cterm list * exporter) list *                      (*assumes: A ==> _*)
        (string * thm list) list) *
      ((string * string) list * string list),              (*fixes: !!x. _*)
    binds: (term * typ) option Vartab.table,               (*term bindings*)
    thms: thm list option Symtab.table,                    (*local thms*)
    cases: (string * RuleCases.T) list,                    (*local contexts*)
    defs:
      typ Vartab.table *                                   (*type constraints*)
      sort Vartab.table *                                  (*default sorts*)
      (string list * term list Symtab.table)};             (*used type variables*)

exception CONTEXT of string * context;


fun make_context (thy, syntax, data, asms, binds, thms, cases, defs) =
  Context {thy = thy, syntax = syntax, data = data, asms = asms, binds = binds,
    thms = thms, cases = cases, defs = defs};

fun map_context f (Context {thy, syntax, data, asms, binds, thms, cases, defs}) =
  make_context (f (thy, syntax, data, asms, binds, thms, cases, defs));

fun theory_of (Context {thy, ...}) = thy;
val sign_of = Theory.sign_of o theory_of;
fun syntax_of (Context {syntax, ...}) = syntax;

fun fixes_of (Context {asms = (_, (fixes, _)), ...}) = fixes;
val fixed_names_of = map #2 o fixes_of;
fun is_fixed (Context {asms = (_, (fixes, _)), ...}) x = exists (equal x o #2) fixes;
fun used_table (Context {defs = (_, _, (_, tab)), ...}) = tab;

fun assumptions_of (Context {asms = ((asms, _), _), ...}) = asms;
fun prems_of (Context {asms = ((_, prems), _), ...}) = flat (map #2 prems);



(** user data **)

(* errors *)

fun of_theory thy = "\nof theory " ^ Sign.str_of_sg (Theory.sign_of thy);

fun err_inconsistent kinds =
  error ("Attempt to merge different versions of " ^ commas_quote kinds ^ " proof data");

fun err_dup_init thy kind =
  error ("Duplicate initialization of " ^ quote kind ^ " proof data" ^ of_theory thy);

fun err_undef ctxt kind =
  raise CONTEXT ("Tried to access undefined " ^ quote kind ^ " proof data", ctxt);

fun err_uninit ctxt kind =
  raise CONTEXT ("Tried to access uninitialized " ^ quote kind ^ " proof data" ^
    of_theory (theory_of ctxt), ctxt);

fun err_access ctxt kind =
  raise CONTEXT ("Unauthorized access to " ^ quote kind ^ " proof data" ^
    of_theory (theory_of ctxt), ctxt);


(* data kind 'Isar/proof_data' *)

structure ProofDataDataArgs =
struct
  val name = "Isar/proof_data";
  type T = (Object.kind * ((theory -> Object.T) * (context -> Object.T -> unit))) Symtab.table;

  val empty = Symtab.empty;
  val copy = I;
  val prep_ext = I;
  fun merge tabs = Symtab.merge (Object.eq_kind o pairself fst) tabs
    handle Symtab.DUPS kinds => err_inconsistent kinds;
  fun print _ tab = Pretty.writeln (Pretty.strs (map #1 (Symtab.dest tab)));
end;

structure ProofDataData = TheoryDataFun(ProofDataDataArgs);
val print_proof_data = ProofDataData.print;


(* init proof data *)

fun init_data kind meths thy =
  let
    val name = Object.name_of_kind kind;
    val tab = Symtab.update_new ((name, (kind, meths)), ProofDataData.get thy)
      handle Symtab.DUP _ => err_dup_init thy name;
  in thy |> ProofDataData.put tab end;


(* access data *)

fun lookup_data (ctxt as Context {data, ...}) kind =
  let
    val thy = theory_of ctxt;
    val name = Object.name_of_kind kind;
  in
    (case Symtab.lookup (ProofDataData.get thy, name) of
      Some (k, meths) =>
        if Object.eq_kind (kind, k) then
          (case Symtab.lookup (data, name) of
            Some x => (x, meths)
          | None => err_undef ctxt name)
        else err_access ctxt name
    | None => err_uninit ctxt name)
  end;

fun get_data kind f ctxt =
  let val (x, _) = lookup_data ctxt kind
  in f x handle Match => Object.kind_error kind end;

fun print_data kind ctxt =
  let val (x, (_, prt)) = lookup_data ctxt kind
  in prt ctxt x end;

fun put_data kind f x ctxt =
 (lookup_data ctxt kind;
  map_context (fn (thy, syntax, data, asms, binds, thms, cases, defs) =>
    (thy, syntax, Symtab.update ((Object.name_of_kind kind, f x), data),
      asms, binds, thms, cases, defs)) ctxt);


(* init context *)

fun init thy =
  let val data = Symtab.map (fn (_, (f, _)) => f thy) (ProofDataData.get thy) in
    make_context (thy, (Theory.syn_of thy, [], []), data, (([], []), ([], [])), Vartab.empty,
      Symtab.empty, [], (Vartab.empty, Vartab.empty, ([], Symtab.empty)))
  end;




(** local syntax **)

val fixedN = "\\<^fixed>";
val structN = "\\<^struct>";


(* add_syntax and syn_of *)

local

val aT = TFree ("'a", logicS);

fun mixfix x None mx = (fixedN ^ x, replicate (Syntax.mixfix_args mx) aT ---> aT, mx)
  | mixfix x (Some T) mx = (fixedN ^ x, T, mx);

fun prep_mixfix (_, _, None) = None
  | prep_mixfix (x, opt_T, Some mx) = Some (mixfix x opt_T mx);

fun prep_mixfix' (_, _, None) = None
  | prep_mixfix' (x, _, Some Syntax.NoSyn) = None
  | prep_mixfix' (x, opt_T, _) = Some (x, mixfix x opt_T (Syntax.Delimfix x));

fun fixed_tr x = (fixedN ^ x, curry Term.list_comb (Syntax.free x));

fun index_tr (Const ("_structs", _) $ Const ("_struct", _) $ idx) = index_tr idx + 1
  | index_tr (Const ("_struct", _)) = 0
  | index_tr t = raise TERM ("index_tr", [t]);

fun struct_app_tr structs [idx, f] =
      let val i = index_tr idx in
        if i < length structs then f $ Syntax.free (Library.nth_elem (i, structs))
        else error ("Illegal reference to structure #" ^ string_of_int (i + 1))
      end
  | struct_app_tr _ ts = raise TERM ("struct_app_tr", ts);

fun prep_struct (x, _, None) = Some x
  | prep_struct _ = None;

in

fun add_syntax decls =
  map_context (fn (thy, (syn, structs, mixfixed), data, asms, binds, thms, cases, defs) =>
    let
      val structs' = structs @ mapfilter prep_struct decls;
      val mxs = mapfilter prep_mixfix decls;
      val (fixed, mxs_output) = Library.split_list (mapfilter prep_mixfix' decls);
      val trs = map fixed_tr fixed;
      val syn' = syn
        |> Syntax.extend_const_gram ("", false) mxs_output
        |> Syntax.extend_const_gram ("", true) mxs
        |> Syntax.extend_trfuns ([], trs, [], []);
    in (thy, (syn', structs', fixed @ mixfixed), data, asms, binds, thms, cases, defs) end)

fun syn_of (Context {syntax = (syn, structs, _), ...}) =
  syn |> Syntax.extend_trfuns ([], [("_struct_app", struct_app_tr structs)], [], []);


end;


(* context_tr' *)

fun context_tr' (Context {syntax = (_, structs, mixfixed), ...}) =
  let
    fun structs_tr' 0 t = t
      | structs_tr' i t = Syntax.const "_structs" $ Syntax.const "_struct" $ structs_tr' (i - 1) t;

    fun tr' (f $ (t as Free (x, T))) =
          let val i = Library.find_index (equal x) structs in
            if i < 0 then tr' f $ tr' t
            else Syntax.const "_struct_app" $ structs_tr' i (Syntax.const "_struct") $ f
          end
      | tr' (t as Free (x, T)) = if x mem_string mixfixed then Const (fixedN ^ x, T) else t
      | tr' (t $ u) = tr' t $ tr' u
      | tr' (Abs (x, T, t)) = Abs (x, T, tr' t)
      | tr' a = a;
  in tr' end;



(** default sorts and types **)

fun def_sort (Context {defs = (_, sorts, _), ...}) xi = Vartab.lookup (sorts, xi);

fun def_type (Context {binds, defs = (types, _, _), ...}) is_pat xi =
  (case Vartab.lookup (types, xi) of
    None =>
      if is_pat then None else
        (case Vartab.lookup (binds, xi) of
          Some (Some (_, T)) => Some (TypeInfer.polymorphicT T)
        | _ => None)
  | some => some);



(** prepare types **)

local

fun read_typ_aux read ctxt s =
  transform_error (read (syn_of ctxt) (sign_of ctxt, def_sort ctxt)) s
    handle ERROR_MESSAGE msg => raise CONTEXT (msg, ctxt);

fun cert_typ_aux cert ctxt raw_T =
  cert (sign_of ctxt) raw_T
    handle TYPE (msg, _, _) => raise CONTEXT (msg, ctxt);

in

val read_typ = read_typ_aux Sign.read_typ';
val read_typ_no_norm = read_typ_aux Sign.read_typ_no_norm';
val cert_typ = cert_typ_aux Sign.certify_typ;
val cert_typ_no_norm = cert_typ_aux Sign.certify_typ_no_norm;

end;


(* internalize Skolem constants *)

fun lookup_skolem ctxt x = assoc (fixes_of ctxt, x);
fun get_skolem ctxt x = if_none (lookup_skolem ctxt x) x;

fun no_skolem no_internal ctxt x =
  if can Syntax.dest_skolem x then
    raise CONTEXT ("Illegal reference to internal Skolem constant: " ^ quote x, ctxt)
  else if no_internal andalso can Syntax.dest_internal x then
    raise CONTEXT ("Illegal reference to internal variable: " ^ quote x, ctxt)
  else x;

fun intern_skolem ctxt =
  let
    fun intern (t as Free (x, T)) =
          (case lookup_skolem ctxt (no_skolem true ctxt x) of
            Some x' => Free (x', T)
          | None => t)
      | intern (t $ u) = intern t $ intern u
      | intern (Abs (x, T, t)) = Abs (x, T, intern t)
      | intern a = a;
  in intern end;


(* externalize Skolem constants -- for printing purposes only *)

fun extern_skolem ctxt =
  let
    val rev_fixes = map Library.swap (fixes_of ctxt);

    fun extern (t as Free (x, T)) =
          (case assoc (rev_fixes, x) of
            Some x' => Free (if lookup_skolem ctxt x' = Some x then x' else NameSpace.hidden x', T)
          | None => t)
      | extern (t $ u) = extern t $ extern u
      | extern (Abs (x, T, t)) = Abs (x, T, extern t)
      | extern a = a;
  in extern end


(** prepare terms and propositions **)

(*
  (1) read / certify wrt. signature of context
  (2) intern Skolem constants
  (3) expand term bindings
*)


(* read / certify wrt. signature *)     (*exception ERROR*) (*exception TERM*)

fun read_def_termTs freeze syn sg (types, sorts, used) sTs =
  Sign.read_def_terms' syn (sg, types, sorts) used freeze sTs;

fun read_def_termT freeze syn sg defs sT = apfst hd (read_def_termTs freeze syn sg defs [sT]);

fun read_term_sg freeze syn sg defs s =
  #1 (read_def_termT freeze syn sg defs (s, TypeInfer.logicT));

fun read_prop_sg freeze syn sg defs s = #1 (read_def_termT freeze syn sg defs (s, propT));

fun read_terms_sg freeze syn sg defs =
  #1 o read_def_termTs freeze syn sg defs o map (rpair TypeInfer.logicT);

fun read_props_sg freeze syn sg defs = #1 o read_def_termTs freeze syn sg defs o map (rpair propT);


fun cert_term_sg sg t = Thm.term_of (Thm.cterm_of sg t);

fun cert_prop_sg sg tm =
  let
    val ctm = Thm.cterm_of sg tm;
    val {t, T, ...} = Thm.rep_cterm ctm;
  in if T = propT then t else raise TERM ("Term not of type prop", [t]) end;


(* norm_term *)

(*beta normal form for terms (not eta normal form), chase variables in
  bindings environment (code taken from Pure/envir.ML)*)

fun unifyT ctxt (T, U) =
  let val maxidx = Int.max (Term.maxidx_of_typ T, Term.maxidx_of_typ U)
  in #1 (Type.unify (Sign.tsig_of (sign_of ctxt)) maxidx Vartab.empty (T, U)) end;

fun norm_term (ctxt as Context {binds, ...}) schematic =
  let
    (*raised when norm has no effect on a term, to do sharing instead of copying*)
    exception SAME;

    fun norm (t as Var (xi, T)) =
          (case Vartab.lookup (binds, xi) of
            Some (Some (u, U)) =>
              let
                val env = unifyT ctxt (T, U) handle Type.TUNIFY =>
                  raise TYPE ("norm_term: ill-typed variable assigment", [T, U], [t, u]);
                val u' = Term.subst_TVars_Vartab env u;
              in norm u' handle SAME => u' end
          | _ =>
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

fun gen_read read app is_pat schematic (ctxt as Context {defs = (_, _, (used, _)), ...}) s =
  (transform_error (read (syn_of ctxt)
      (sign_of ctxt) (def_type ctxt is_pat, def_sort ctxt, used)) s
    handle TERM (msg, _) => raise CONTEXT (msg, ctxt)
    | ERROR_MESSAGE msg => raise CONTEXT (msg, ctxt))
  |> app (intern_skolem ctxt)
  |> app (if is_pat then I else norm_term ctxt schematic)
  |> app (if is_pat then prepare_dummies else (reject_dummies ctxt));

in

val read_termTs = gen_read (read_def_termTs false) (apfst o map) false false;
val read_termT_pats = #1 oo gen_read (read_def_termTs false) (apfst o map) true false;

fun read_term_pats T ctxt pats = read_termT_pats ctxt (map (rpair T) pats);
val read_prop_pats = read_term_pats propT;

val read_term = gen_read (read_term_sg true) I false false;
val read_prop = gen_read (read_prop_sg true) I false false;
val read_prop_schematic = gen_read (read_prop_sg true) I false true;
val read_terms = gen_read (read_terms_sg true) map false false;
val read_props = gen_read (read_props_sg true) map false;

end;


(* certify terms *)

local

fun gen_cert cert is_pat schematic ctxt t = t
  |> (if is_pat then I else norm_term ctxt schematic)
  |> (fn t' => cert (sign_of ctxt) t' handle TERM (msg, _) => raise CONTEXT (msg, ctxt));

in

val cert_term = gen_cert cert_term_sg false false;
val cert_prop = gen_cert cert_prop_sg false false;
val cert_props = map oo gen_cert cert_prop_sg false;

fun cert_term_pats _ = map o gen_cert cert_term_sg true false;
val cert_prop_pats = map o gen_cert cert_prop_sg true false;

end;


(* declare terms *)

local

val ins_types = foldl_aterms
  (fn (types, Free (x, T)) => Vartab.update (((x, ~1), T), types)
    | (types, Var v) => Vartab.update (v, types)
    | (types, _) => types);

val ins_sorts = foldl_types (foldl_atyps
  (fn (sorts, TFree (x, S)) => Vartab.update (((x, ~1), S), sorts)
    | (sorts, TVar v) => Vartab.update (v, sorts)
    | (sorts, _) => sorts));

val ins_used = foldl_term_types (fn t => foldl_atyps
  (fn ((used, tab), TFree (x, _)) => (x ins used, Symtab.update_multi ((x, t), tab))
    | (used, _) => used));

fun ins_skolem def_ty = foldr
  (fn ((x, x'), types) =>
    (case def_ty x' of
      Some T => Vartab.update (((x, ~1), T), types)
    | None => types));

fun map_defaults f = map_context (fn (thy, syntax, data, asms, binds, thms, cases, defs) =>
  (thy, syntax, data, asms, binds, thms, cases, f defs));

fun declare_syn (ctxt, t) =
  ctxt
  |> map_defaults (fn (types, sorts, used) => (ins_types (types, t), sorts, used))
  |> map_defaults (fn (types, sorts, used) => (types, ins_sorts (sorts, t), used));

fun declare_occ (ctxt as Context {asms = (_, (fixes, _)), ...}, t) =
  declare_syn (ctxt, t)
  |> map_defaults (fn (types, sorts, used) => (types, sorts, ins_used (used, t)))
  |> map_defaults (fn (types, sorts, used) =>
      (ins_skolem (fn x => Vartab.lookup (types, (x, ~1))) (fixes, types), sorts, used));

in

fun declare_term t ctxt = declare_occ (ctxt, t);
fun declare_terms ts ctxt = foldl declare_occ (ctxt, ts);
fun predeclare_terms ts ctxt = foldl declare_syn (ctxt, ts);

end;



(** pretty printing **)

fun pretty_term ctxt = Sign.pretty_term' (syn_of ctxt) (sign_of ctxt) o context_tr' ctxt;
val pretty_typ = Sign.pretty_typ o sign_of;
val pretty_sort = Sign.pretty_sort o sign_of;

val string_of_term = Pretty.string_of oo pretty_term;

val show_hyps = ref false;

fun pretty_thm ctxt thm =
  if ! show_hyps then setmp Display.show_hyps true (fn () =>
    Display.pretty_thm_aux (pretty_sort ctxt, pretty_term ctxt) false thm) ()
  else pretty_term ctxt (#prop (Thm.rep_thm thm));

fun pretty_thms ctxt [th] = pretty_thm ctxt th
  | pretty_thms ctxt ths = Pretty.blk (0, Pretty.fbreaks (map (pretty_thm ctxt) ths));



(** Hindley-Milner polymorphism **)

(* warn_extra_tfrees *)

local

fun used_free (a, ts) =
  (case mapfilter (fn Free (x, _) => Some x | _ => None) ts of
    [] => None
  | xs => Some (a, xs));

fun warn_extra (names1: string list, tab1) (names2, tab2) =
  if names1 = names2 then ()
  else
    let
      val extra =
        Library.gen_rems Library.eq_fst (Symtab.dest tab2, Symtab.dest tab1)
        |> mapfilter used_free;
      val tfrees = map #1 extra;
      val frees = Library.sort_strings (Library.distinct (flat (map #2 extra)));
    in
      if null extra then ()
      else warning ("Just introduced free type variable(s): " ^ commas tfrees ^ " in " ^
          space_implode " or " frees)
    end;

in

fun warn_extra_tfrees (ctxt1 as Context {defs = (_, _, used1), ...})
    (ctxt2 as Context {defs = (_, _, used2), ...}) = (warn_extra used1 used2; ctxt2);

end;


(* generalize type variables *)

fun gen_tfrees inner outer =
  let
    val extra_fixes = fixed_names_of inner \\ fixed_names_of outer;
    fun still_fixed (Free (x, _)) = not (x mem_string extra_fixes)
      | still_fixed _ = false;
    fun add (gen, (a, xs)) =
      if is_some (Symtab.lookup (used_table outer, a)) orelse exists still_fixed xs
      then gen else a :: gen;
  in Symtab.foldl add ([], used_table inner) end;

fun generalizeT inner outer =
  let
    val tfrees = gen_tfrees inner outer;
    fun gen (x, S) = if x mem_string tfrees then TVar ((x, 0), S) else TFree (x, S);
  in Term.map_type_tfree gen end;

val generalize = Term.map_term_types oo generalizeT;



(** export theorems **)

fun get_free x (None, t as Free (y, _)) = if x = y then Some t else None
  | get_free _ (opt, _) = opt;

fun find_free t x = foldl_aterms (get_free x) (None, t);

fun export is_goal inner outer =
  let
    val tfrees = gen_tfrees inner outer;
    val fixes = fixed_names_of inner \\ fixed_names_of outer;
    val asms = Library.drop (length (assumptions_of outer), assumptions_of inner);
    val exp_asms = map (fn (cprops, exp) => exp is_goal cprops) asms;
  in fn thm =>
    thm
    |> Tactic.norm_hhf
    |> Seq.EVERY (rev exp_asms)
    |> Seq.map (fn rule =>
      let
        val {sign, prop, ...} = Thm.rep_thm rule;
        val frees = map (Thm.cterm_of sign) (mapfilter (find_free prop) fixes);
      in
        rule
        |> Drule.forall_intr_list frees
        |> Tactic.norm_hhf
        |> Drule.tvars_intr_list tfrees
      end)
  end;



(** bindings **)

(* update_binds *)

fun del_bind (ctxt, xi) =
  ctxt
  |> map_context (fn (thy, syntax, data, asms, binds, thms, cases, defs) =>
      (thy, syntax, data, asms, Vartab.update ((xi, None), binds), thms, cases, defs));

fun upd_bind (ctxt, ((x, i), t)) =
  let
    val T = Term.fastype_of t;
    val t' =
      if null (Term.term_tvars t \\ Term.typ_tvars T) then t
      else Var ((x ^ "_has_extra_type_vars_on_rhs", i), T);
  in
    ctxt
    |> declare_term t'
    |> map_context (fn (thy, syntax, data, asms, binds, thms, cases, defs) =>
      (thy, syntax, data, asms, Vartab.update (((x, i), Some (t', T)), binds), thms, cases, defs))
  end;

fun del_upd_bind (ctxt, (xi, None)) = del_bind (ctxt, xi)
  | del_upd_bind (ctxt, (xi, Some t)) = upd_bind (ctxt, (xi, t));

fun update_binds bs ctxt = foldl upd_bind (ctxt, bs);
fun delete_update_binds bs ctxt = foldl del_upd_bind (ctxt, bs);


(* simult_matches *)

local

val add_vars = Term.foldl_aterms (fn (vs, Var (xi, _)) => xi ins vs | (vs, _) => vs);
fun vars_of ts = foldl add_vars ([], ts);

in

fun simult_matches ctxt [] = []
  | simult_matches ctxt pairs =
      let
        fun fail () = raise CONTEXT ("Pattern match failed!", ctxt);

        val maxidx = foldl (fn (i, (t1, t2)) =>
          Int.max (i, Int.max (Term.maxidx_of_term t1, Term.maxidx_of_term t2))) (~1, pairs);
        val envs = Unify.smash_unifiers (sign_of ctxt, Envir.empty maxidx,
          map swap pairs);    (*prefer assignment of variables from patterns*)
        val env =
          (case Seq.pull envs of
            None => fail ()
          | Some (env, _) => env);    (*ignore further results*)
        val domain = filter_out Term.is_replaced_dummy_pattern (vars_of (map #1 pairs));
        val _ =    (*may not assign variables from text*)
          if null (map #1 (Envir.alist_of env) inter vars_of (map #2 pairs)) then ()
          else fail ();
        fun norm_bind (xi, t) = if xi mem domain then Some (xi, Envir.norm_term env t) else None;
      in mapfilter norm_bind (Envir.alist_of env) end;

end;


(* add_binds(_i) *)

local

fun gen_bind prep (ctxt, (xi as (x, _), raw_t)) =
  ctxt |> delete_update_binds [(xi, apsome (prep ctxt) raw_t)];

fun gen_binds prep binds ctxt = foldl (gen_bind prep) (ctxt, binds);

in

fun drop_schematic (b as (xi, Some t)) = if null (Term.term_vars t) then b else (xi, None)
  | drop_schematic b = b;

val add_binds = gen_binds read_term;
val add_binds_i = gen_binds cert_term;

fun auto_bind_goal t ctxt =
  ctxt |> add_binds_i (map drop_schematic (AutoBind.goal (sign_of ctxt) t));

fun auto_bind_facts name ts ctxt =
  ctxt |> add_binds_i (map drop_schematic (AutoBind.facts (sign_of ctxt) name ts));

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
      apsnd flat (foldl_map (prep_bind prep_pats) (ctxt, map fst raw_binds ~~ ts));
    val binds' =
      if gen then map (apsnd (generalize ctxt' ctxt)) binds
      else binds;
    val binds'' = map (apsnd Some) binds';
  in
    warn_extra_tfrees ctxt
     (if gen then ctxt (*sic!*) |> declare_terms (map #2 binds') |> add_binds_i binds''
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
            val len1 = length raw_pats1;
          in ((ctxt', props), (prop, (take (len1, pats), drop (len1, pats)))) end
      | prep _ = sys_error "prep_propp";
    val ((context', _), propp) = foldl_map (foldl_map prep)
        ((context, prep_props schematic context (flat (map (map fst) args))), args);
  in (context', propp) end;

fun matches ctxt (prop, (pats1, pats2)) =
  simult_matches ctxt (map (rpair prop) pats1 @ map (rpair (Logic.strip_imp_concl prop)) pats2);

fun gen_bind_propp prepp (ctxt, raw_args) =
  let
    val (ctxt', args) = prepp (ctxt, raw_args);
    val binds = flat (flat (map (map (matches ctxt')) args));
    val propss = map (map #1) args;

    (*generalize result: context evaluated now, binds added later*)
    val gen = generalize ctxt' ctxt;
    fun gen_binds c = c |> add_binds_i (map (apsnd (Some o gen)) binds);
  in (ctxt' |> add_binds_i (map (apsnd Some) binds), (propss, gen_binds)) end;

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

fun retrieve_thms f g (ctxt as Context {thy, thms, ...}) =
  let
    val sg_ref = Sign.self_ref (Theory.sign_of thy);
    val get_from_thy = f thy;
  in
    fn name =>
      (case Symtab.lookup (thms, name) of
        Some (Some ths) => map (Thm.transfer_sg (Sign.deref sg_ref)) ths
      | _ => get_from_thy name) |> g name
  end;

val get_thm = retrieve_thms PureThy.get_thms PureThy.single_thm;
val get_thm_closure = retrieve_thms PureThy.get_thms_closure PureThy.single_thm;
val get_thms = retrieve_thms PureThy.get_thms (K I);
val get_thms_closure = retrieve_thms PureThy.get_thms_closure (K I);


(* put_thm(s) *)

fun put_thms ("", _) = I
  | put_thms (name, ths) = map_context
      (fn (thy, syntax, data, asms, binds, thms, cases, defs) =>
        (thy, syntax, data, asms, binds, Symtab.update ((name, Some ths), thms), cases, defs));

fun put_thm (name, th) = put_thms (name, [th]);

fun put_thmss [] ctxt = ctxt
  | put_thmss (th :: ths) ctxt = ctxt |> put_thms th |> put_thmss ths;


(* reset_thms *)

fun reset_thms name = map_context (fn (thy, syntax, data, asms, binds, thms, cases, defs) =>
  (thy, syntax, data, asms, binds, Symtab.update ((name, None), thms), cases, defs));


(* have_thmss *)

fun have_thss (ctxt, ((name, more_attrs), ths_attrs)) =
  let
    fun app ((ct, ths), (th, attrs)) =
      let val (ct', th') = Thm.applys_attributes ((ct, th), attrs @ more_attrs)
      in (ct', th' :: ths) end
    val (ctxt', rev_thms) = foldl app ((ctxt, []), ths_attrs);
    val thms = flat (rev rev_thms);
  in (ctxt' |> put_thms (name, thms), (name, thms)) end;

fun have_thmss args ctxt = foldl_map have_thss (ctxt, args);



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
      err "Head of lhs must be free or fixed variable";

    fun is_free (Free (x, _)) = not (is_fixed ctxt x)
      | is_free _ = false;
    val extra_frees = filter is_free (term_frees rhs) \\ xs;
  in
    conditional (not (forall (is_Bound orf is_free) xs andalso null (duplicates xs))) (fn () =>
      err "Arguments of lhs must be distinct free or fixed variables");
    conditional (f mem Term.term_frees rhs) (fn () =>
      err "Element to be defined occurs on rhs");
    conditional (not (null extra_frees)) (fn () =>
      err ("Extra free variables on rhs: " ^ commas_quote (map (#1 o dest_Free) extra_frees)));
    (c, Term.list_all_free (mapfilter (try Term.dest_Free) xs, eq))
  end;

fun head_of_def cprop =
  #1 (Term.strip_comb (#1 (Logic.dest_equals (Term.strip_all_body (Thm.term_of cprop)))))
  |> Thm.cterm_of (Thm.sign_of_cterm cprop);

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
    val cprops = map (Thm.cterm_of (sign_of ctxt)) props;
    val asms = map (Tactic.norm_hhf o Thm.assume) cprops;

    val ths = map (fn th => ([th], [])) asms;
    val (ctxt', [(_, thms)]) =
      ctxt
      |> auto_bind_facts name props
      |> have_thmss [((name, attrs), ths)];
  in (ctxt', (cprops, (name, asms), (name, thms))) end;

fun gen_assms prepp exp args ctxt =
  let
    val (ctxt1, propss) = prepp (ctxt, map snd args);
    val (ctxt2, results) = foldl_map add_assm (ctxt1, map fst args ~~ propss);

    val cprops = flat (map #1 results);
    val asmss = map #2 results;
    val thmss = map #3 results;
    val ctxt3 = ctxt2 |> map_context
      (fn (thy, syntax, data, ((asms_ct, asms_th), fixes), binds, thms, cases, defs) =>
        (thy, syntax, data, ((asms_ct @ [(cprops, exp)], asms_th @ asmss), fixes), binds, thms,
          cases, defs));
    val ctxt4 = ctxt3 |> put_thms ("prems", prems_of ctxt3);
  in (warn_extra_tfrees ctxt ctxt4, thmss) end;

in

val assume = gen_assms (apsnd #1 o bind_propp);
val assume_i = gen_assms (apsnd #1 o bind_propp_i);

end;


(* variables *)

local

fun prep_vars prep_typ no_internal (ctxt, (xs, raw_T)) =
  let
    val _ = (case filter (not o Syntax.is_identifier) (map (no_skolem no_internal ctxt) xs) of
      [] => () | bads => raise CONTEXT ("Bad variable name(s): " ^ commas_quote bads, ctxt));

    val opt_T = apsome (prep_typ ctxt) raw_T;
    val T = if_none opt_T TypeInfer.logicT;
    val ctxt' = ctxt |> predeclare_terms (map (fn x => Free (x, T)) xs);
  in (ctxt', (xs, opt_T)) end;

in

val read_vars = prep_vars read_typ true;
val cert_vars = prep_vars cert_typ false;

end;


(* fix *)

local

fun map_vars f = map_context (fn (thy, syntax, data, (assumes, vars), binds, thms, cases, defs) =>
  (thy, syntax, data, (assumes, f vars), binds, thms, cases, defs));

fun err_dups ctxt xs = raise CONTEXT ("Duplicate variable(s): " ^ commas_quote xs, ctxt);

fun add_vars _ xs (fixes, used) =
  let
    val xs' = variantlist (xs, used);
    val fixes' = (xs ~~ map Syntax.skolem xs') @ fixes;
    val used' = xs' @ used;
  in (fixes', used') end;

fun add_vars_direct ctxt xs (fixes, used) =
  (case xs inter_string map #1 fixes of
    [] => ((xs ~~ xs) @ fixes, xs @ used)
  | dups => err_dups ctxt dups);

fun gen_fix prep add raw_vars ctxt =
  let
    val (ctxt', varss) = foldl_map prep (ctxt, raw_vars);
    val xs = flat (map fst varss);
  in
    (case Library.duplicates xs of [] => () | dups => err_dups ctxt dups);
    ctxt' |> map_vars (add ctxt (rev xs))
  end;

in

val fix = gen_fix read_vars add_vars;
val fix_i = gen_fix cert_vars add_vars;
val fix_direct = gen_fix cert_vars add_vars_direct;

end;

fun fix_frees ts ctxt =
  let
    val frees = foldl Drule.add_frees ([], ts);
    fun new (x, T) = if is_fixed ctxt x then None else Some ([x], Some T);
  in fix_direct (mapfilter new frees) ctxt end;


(*Note: improper use may result in variable capture / dynamic scoping!*)
fun bind_skolem ctxt xs =
  let
    val ctxt' = ctxt |> fix_i [(xs, None)];
    fun bind (t as Free (x, T)) =
          if x mem_string xs then
            (case lookup_skolem ctxt' x of Some x' => Free (x', T) | None => t)
          else t
      | bind (t $ u) = bind t $ bind u
      | bind (Abs (x, T, t)) = Abs (x, T, bind t)
      | bind a = a;
  in bind end;



(** cases **)

fun prep_case ctxt name xs {fixes, assumes, binds} =
  let
    fun replace (opt_x :: xs) ((y, T) :: ys) = (if_none opt_x y, T) :: replace xs ys
      | replace [] ys = ys
      | replace (_ :: _) [] = raise CONTEXT ("Too many parameters for case " ^ quote name, ctxt);
  in
    if null (foldr Term.add_typ_tvars (map snd fixes, [])) andalso
      null (foldr Term.add_term_vars (assumes, [])) then
        {fixes = replace xs fixes, assumes = assumes, binds = map drop_schematic binds}
    else raise CONTEXT ("Illegal schematic variable(s) in case " ^ quote name, ctxt)
  end;

fun get_case (ctxt as Context {cases, ...}) name xs =
  (case assoc (cases, name) of
    None => raise CONTEXT ("Unknown case: " ^ quote name, ctxt)
  | Some c => prep_case ctxt name xs c);


fun add_cases xs = map_context (fn (thy, syntax, data, asms, binds, thms, cases, defs) =>
  (thy, syntax, data, asms, binds, thms, rev (filter_out (equal "" o #1) xs) @ cases, defs));



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

val smash_option = fn (_, None) => None | (xi, Some b) => Some (xi, b);

fun pretty_binds (ctxt as Context {binds, ...}) =
  let
    fun prt_bind (xi, (t, T)) = pretty_term ctxt (Logic.mk_equals (Var (xi, T), t));
    val bs = mapfilter smash_option (Vartab.dest binds);
  in
    if null bs andalso not (! verbose) then []
    else [Pretty.big_list "term bindings:" (map prt_bind bs)]
  end;

val print_binds = Pretty.writeln o Pretty.chunks o pretty_binds;


(* local theorems *)

fun pretty_lthms (ctxt as Context {thms, ...}) =
  pretty_items (pretty_thm ctxt) "facts:" (mapfilter smash_option (Symtab.dest thms));

val print_lthms = Pretty.writeln o Pretty.chunks o pretty_lthms;


(* local contexts *)

fun apply_case ({fixes, assumes, binds}: RuleCases.T) ctxt =
  let
    fun bind (c, (x, T)) = (c |> fix_i [([x], Some T)], bind_skolem c [x] (Free (x, T)));
    val (ctxt', xs) = foldl_map bind (ctxt, fixes);
    fun app t = foldl Term.betapply (t, xs);
  in (ctxt', (map (apsnd (apsome app)) binds, map app assumes)) end;

fun pretty_cases (ctxt as Context {cases, ...}) =
  let
    val prt_term = pretty_term ctxt;

    fun prt_let (xi, t) = Pretty.block
      [Pretty.quote (prt_term (Var (xi, Term.fastype_of t))), Pretty.str " =", Pretty.brk 1,
        Pretty.quote (prt_term t)];

    fun prt_sect _ _ _ [] = []
      | prt_sect s sep prt xs = [Pretty.block (Pretty.breaks (Pretty.str s ::
            flat (Library.separate sep (map (Library.single o prt) xs))))];

    fun prt_case (name, (fixes, (lets, asms))) = Pretty.block (Pretty.fbreaks
      (Pretty.str (name ^ ":") ::
        prt_sect "fix" [] (Pretty.str o fst) fixes @
        prt_sect "let" [Pretty.str "and"] prt_let
          (mapfilter (fn (xi, Some t) => Some (xi, t) | _ => None) lets) @
        prt_sect "assume" [] (Pretty.quote o prt_term) asms));

    val cases' = rev (Library.gen_distinct Library.eq_fst cases);
  in
    if null cases andalso not (! verbose) then []
    else [Pretty.big_list "cases:"
      (map (prt_case o apsnd (fn c => (#fixes c, #2 (apply_case c ctxt)))) cases')]
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

fun pretty_context (ctxt as Context {cases, defs = (types, sorts, (used, _)), ...}) =
  let
    val prt_term = pretty_term ctxt;
    val prt_typ = pretty_typ ctxt;
    val prt_sort = pretty_sort ctxt;

    (*theory*)
    val pretty_thy = Pretty.block
      [Pretty.str "Theory:", Pretty.brk 1, Sign.pretty_sg (sign_of ctxt)];

    (*defaults*)
    fun prt_atom prt prtT (x, X) = Pretty.block
      [prt x, Pretty.str " ::", Pretty.brk 1, prtT X];

    fun prt_var (x, ~1) = prt_term (Syntax.free x)
      | prt_var xi = prt_term (Syntax.var xi);

    fun prt_varT (x, ~1) = prt_typ (TFree (x, []))
      | prt_varT xi = prt_typ (TVar (xi, []));

    val prt_defT = prt_atom prt_var prt_typ;
    val prt_defS = prt_atom prt_varT prt_sort;
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



(** theory setup **)

val setup = [ProofDataData.init];

end;
