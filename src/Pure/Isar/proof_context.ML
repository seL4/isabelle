(*  Title:      Pure/Isar/proof_context.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Proof context information.
*)

signature PROOF_CONTEXT =
sig
  type context
  exception CONTEXT of string * context
  val theory_of: context -> theory
  val sign_of: context -> Sign.sg
  val prems_of: context -> thm list
  val show_hyps: bool ref
  val pretty_thm: thm -> Pretty.T
  val verbose: bool ref
  val print_binds: context -> unit
  val print_thms: context -> unit
  val print_cases: context -> unit
  val pretty_prems: context -> Pretty.T list
  val pretty_context: context -> Pretty.T list
  val print_proof_data: theory -> unit
  val init: theory -> context
  val assumptions: context -> (cterm * ((int -> tactic) * (int -> tactic))) list
  val fixed_names: context -> string list
  val read_typ: context -> string -> typ
  val cert_typ: context -> typ -> typ
  val cert_skolem: context -> string -> string
  val read_termTs: context -> (string * typ) list -> term list * (indexname * typ) list
  val read_term: context -> string -> term
  val read_prop: context -> string -> term
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
  val export_wrt: context -> context option
    -> (thm -> thm) * ((int -> tactic) * (int -> tactic)) list
  val auto_bind_goal: term -> context -> context
  val auto_bind_facts: string -> term list -> context -> context
  val match_bind: bool -> (string list * string) list -> context -> context
  val match_bind_i: bool -> (term list * term) list -> context -> context
  val read_propp: context * (string * (string list * string list))
    -> context * (term * (term list * term list))
  val cert_propp: context * (term * (term list * term list))
    -> context * (term * (term list * term list))
  val bind_propp: context * (string * (string list * string list))
    -> context * (term * (context -> context))
  val bind_propp_i: context * (term * (term list * term list))
    -> context * (term * (context -> context))
  val get_thm: context -> string -> thm
  val get_thms: context -> string -> thm list
  val get_thmss: context -> string list -> thm list
  val put_thm: string * thm -> context -> context
  val put_thms: string * thm list -> context -> context
  val put_thmss: (string * thm list) list -> context -> context
  val reset_thms: string -> context -> context
  val have_thmss: thm list -> string -> context attribute list
    -> (thm list * context attribute list) list -> context -> context * (string * thm list)
  val assume: ((int -> tactic) * (int -> tactic))
    -> (string * context attribute list * (string * (string list * string list)) list) list
    -> context -> context * ((string * thm list) list * thm list)
  val assume_i: ((int -> tactic) * (int -> tactic))
    -> (string * context attribute list * (term * (term list * term list)) list) list
    -> context -> context * ((string * thm list) list * thm list)
  val read_vars: context * (string list * string option) -> context * (string list * typ option)
  val cert_vars: context * (string list * typ option) -> context * (string list * typ option)
  val fix: (string list * string option) list -> context -> context
  val fix_i: (string list * typ option) list -> context -> context
  val get_case: context -> string -> RuleCases.T
  val add_cases: (string * RuleCases.T) list -> context -> context
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

datatype context =
  Context of
   {thy: theory,                                                        (*current theory*)
    data: Object.T Symtab.table,                                        (*user data*)
    asms:
      ((cterm * ((int -> tactic) * (int -> tactic))) list *             (*assumes: A ==> _*)
        (string * thm list) list) *
      ((string * string) list * string list),                           (*fixes: !!x. _*)
    binds: (term * typ) option Vartab.table,                            (*term bindings*)
    thms: thm list option Symtab.table,                                 (*local thms*)
    cases: (string * RuleCases.T) list,                                 (*local contexts*)
    defs:
      typ Vartab.table *                                                (*type constraints*)
      sort Vartab.table *                                               (*default sorts*)
      (string list * term list Symtab.table)};                          (*used type variables*)

exception CONTEXT of string * context;


fun make_context (thy, data, asms, binds, thms, cases, defs) =
  Context {thy = thy, data = data, asms = asms, binds = binds, thms = thms,
    cases = cases, defs = defs};

fun map_context f (Context {thy, data, asms, binds, thms, cases, defs}) =
  make_context (f (thy, data, asms, binds, thms, cases, defs));

fun theory_of (Context {thy, ...}) = thy;
val sign_of = Theory.sign_of o theory_of;

fun prems_of (Context {asms = ((_, asms), _), ...}) = flat (map #2 asms);



(** print context information **)

val show_hyps = ref false;

fun pretty_thm thm =
  if ! show_hyps then setmp Display.show_hyps true Display.pretty_thm_no_quote thm
  else Display.pretty_cterm (#prop (Thm.crep_thm thm));

val verbose = ref false;
fun verb f x = if ! verbose then f (x ()) else [];
fun verb_single x = verb Library.single x;

fun pretty_items prt name items =
  let
    fun prt_itms (name, [x]) = Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1, prt x]
      | prt_itms (name, xs) = Pretty.big_list (name ^ ":") (map prt xs);
  in
    if null items andalso not (! verbose) then []
    else [Pretty.big_list name (map prt_itms items)]
  end;


(* term bindings *)

val smash_option = fn (_, None) => None | (xi, Some b) => Some (xi, b);

fun pretty_binds (ctxt as Context {binds, ...}) =
  let
    val prt_term = Sign.pretty_term (sign_of ctxt);
    fun prt_bind (xi, (t, T)) = prt_term (Logic.mk_equals (Var (xi, T), t));
    val bs = mapfilter smash_option (Vartab.dest binds);
  in
    if null bs andalso not (! verbose) then []
    else [Pretty.big_list "term bindings:" (map prt_bind bs)]
  end;

val print_binds = Pretty.writeln o Pretty.chunks o pretty_binds;


(* local theorems *)

fun pretty_thms (Context {thms, ...}) =
  pretty_items pretty_thm "local theorems:" (mapfilter smash_option (Symtab.dest thms));

val print_thms = Pretty.writeln o Pretty.chunks o pretty_thms;


(* local contexts *)

fun pretty_cases (ctxt as Context {cases, ...}) =
  let
    val prt_term = Sign.pretty_term (sign_of ctxt);

    fun prt_sect _ _ [] = []
      | prt_sect s prt xs = [Pretty.block (Pretty.breaks (Pretty.str s :: map prt xs))];

    fun prt_case (name, (xs, ts)) = Pretty.block (Pretty.breaks
      (Pretty.str (name ^ ":") ::
        prt_sect "fix" (prt_term o Free) xs @
        prt_sect "assume" (Pretty.quote o prt_term) ts));

    val cases' = rev (Library.gen_distinct Library.eq_fst cases);
  in
    if null cases andalso not (! verbose) then []
    else [Pretty.big_list "cases:" (map prt_case cases')]
  end;

val print_cases = Pretty.writeln o Pretty.chunks o pretty_cases;


(* main context *)

fun pretty_prems ctxt =
  (case prems_of ctxt of
    [] => []
  | prems => [Pretty.big_list "prems:" (map pretty_thm prems)]);

fun pretty_context (ctxt as Context {asms = (_, (fixes, _)), cases,
    defs = (types, sorts, (used, _)), ...}) =
  let
    val sign = sign_of ctxt;

    val prt_term = Sign.pretty_term sign;
    val prt_typ = Sign.pretty_typ sign;
    val prt_sort = Sign.pretty_sort sign;

    (*theory*)
    val pretty_thy = Pretty.block [Pretty.str "Theory:", Pretty.brk 1, Sign.pretty_sg sign];

    (*fixes*)
    fun prt_fix (x, x') = Pretty.block
      [prt_term (Syntax.free x), Pretty.str " =", Pretty.brk 1, prt_term (Syntax.free x')];

    fun prt_fixes xs = Pretty.block (Pretty.str "fixed variables:" :: Pretty.brk 1 ::
      Pretty.commas (map prt_fix xs));

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
    (if null fixes then [] else [prt_fixes (rev fixes)]) @
    pretty_prems ctxt @
    verb pretty_binds (K ctxt) @
    verb pretty_thms (K ctxt) @
    verb pretty_cases (K ctxt) @
    verb_single (fn () => Pretty.big_list "type constraints:" (map prt_defT (Vartab.dest types))) @
    verb_single (fn () => Pretty.big_list "default sorts:" (map prt_defS (Vartab.dest sorts))) @
    verb_single (fn () => Pretty.strs ("used type variable names:" :: used))
  end;



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
  ctxt |> map_context (fn (thy, data, asms, binds, thms, cases, defs) =>
    (thy, Symtab.update ((Object.name_of_kind kind, f x), data), asms, binds, thms, cases, defs)));


(* init context *)

fun init thy =
  let val data = Symtab.map (fn (_, (f, _)) => f thy) (ProofDataData.get thy) in
    make_context (thy, data, (([], []), ([], [])), Vartab.empty, Symtab.empty, [],
      (Vartab.empty, Vartab.empty, ([], Symtab.empty)))
  end;


(* get assumptions *)

fun assumptions (Context {asms = ((asms, _), _), ...}) = asms;
fun fixed_names (Context {asms = (_, (fixes, _)), ...}) = map #2 fixes;
fun used_table (Context {defs = (_, _, (_, tab)), ...}) = tab;



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

fun read_typ ctxt s =
  transform_error (Sign.read_typ (sign_of ctxt, def_sort ctxt)) s
    handle ERROR_MESSAGE msg => raise CONTEXT (msg, ctxt);

fun cert_typ ctxt raw_T =
  Sign.certify_typ (sign_of ctxt) raw_T
    handle TYPE (msg, _, _) => raise CONTEXT (msg, ctxt);


(* internalize Skolem constants *)

fun get_skolem (Context {asms = (_, (fixes, _)), ...}) x = assoc (fixes, x);

fun check_skolem ctxt check x =
  if check andalso can Syntax.dest_skolem x then
    raise CONTEXT ("Illegal reference to internal Skolem constant: " ^ quote x, ctxt)
  else x;

fun intern_skolem ctxt check =
  let
    fun intern (t as Free (x, T)) =
          (case get_skolem ctxt (check_skolem ctxt check x) of
            Some x' => Free (x', T)
          | None => t)
      | intern (t $ u) = intern t $ intern u
      | intern (Abs (x, T, t)) = Abs (x, T, intern t)
      | intern a = a;
  in intern end;

fun cert_skolem ctxt x =
  (case get_skolem ctxt x of
    None => raise CONTEXT ("Undeclared variable: " ^ quote x, ctxt)
  | Some x' => x');



(** prepare terms and propositions **)

(*
  (1) read / certify wrt. signature of context
  (2) intern Skolem constants
  (3) expand term bindings
*)


(* read / certify wrt. signature *)     (*exception ERROR*) (*exception TERM*)

fun read_def_termTs freeze sg (types, sorts, used) sTs =
  Sign.read_def_terms (sg, types, sorts) used freeze sTs;

fun read_def_termT freeze sg defs sT = apfst hd (read_def_termTs freeze sg defs [sT]);

fun read_term_sg freeze sg defs s = #1 (read_def_termT freeze sg defs (s, TypeInfer.logicT));
fun read_prop_sg freeze sg defs s = #1 (read_def_termT freeze sg defs (s, propT));


fun cert_term_sg sg t = Thm.term_of (Thm.cterm_of sg t);

fun cert_prop_sg sg tm =
  let
    val ctm = Thm.cterm_of sg tm;
    val {t, T, ...} = Thm.rep_cterm ctm;
  in
    if T = propT then t
    else raise TERM ("Term not of type prop", [t])
  end;


(* norm_term *)

(*beta normal form for terms (not eta normal form), chase variables in
  bindings environment (code taken from Pure/envir.ML)*)

fun unifyT ctxt (T, U) =
  let val maxidx = Int.max (Term.maxidx_of_typ T, Term.maxidx_of_typ U)
  in #1 (Type.unify (Sign.tsig_of (sign_of ctxt)) maxidx Vartab.empty (T, U)) end;

fun norm_term (ctxt as Context {binds, ...}) =
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
          | _ => raise CONTEXT ("Unbound schematic variable: " ^ Syntax.string_of_vname xi, ctxt))
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

local

fun is_dummy (Const (c, _)) = c = PureThy.dummy_patternN
  | is_dummy _ = false;

fun prep_dummy (i, t) =
  if is_dummy t then (i + 1, Var (("_dummy_", i), Term.fastype_of t)) else (i, t);

in

fun prepare_dummies tm = #2 (Term.foldl_map_aterms prep_dummy (1, tm));

fun reject_dummies ctxt tm =
  if foldl_aterms (fn (ok, t) => ok andalso not (is_dummy t)) (true, tm) then tm
  else raise CONTEXT ("Illegal dummy pattern(s) in term", ctxt);

end;


(* read terms *)

fun gen_read read app is_pat (ctxt as Context {defs = (_, _, (used, _)), ...}) s =
  (transform_error (read (sign_of ctxt) (def_type ctxt is_pat, def_sort ctxt, used)) s
    handle TERM (msg, _) => raise CONTEXT (msg, ctxt)
    | ERROR_MESSAGE msg => raise CONTEXT (msg, ctxt))
  |> app (intern_skolem ctxt true)
  |> app (if is_pat then I else norm_term ctxt)
  |> app (if is_pat then prepare_dummies else (reject_dummies ctxt));

val read_termTs = gen_read (read_def_termTs false) (apfst o map) false;
val read_termT_pats = #1 oo gen_read (read_def_termTs false) (apfst o map) true;

fun read_term_pats T ctxt pats = read_termT_pats ctxt (map (rpair T) pats);
val read_prop_pats = read_term_pats propT;

val read_term = gen_read (read_term_sg true) I false;
val read_prop = gen_read (read_prop_sg true) I false;


(* certify terms *)

fun gen_cert cert is_pat ctxt t = t
  |> intern_skolem ctxt false
  |> (if is_pat then I else norm_term ctxt)
  |> (fn t' => cert (sign_of ctxt) t' handle TERM (msg, _) => raise CONTEXT (msg, ctxt));

val cert_term = gen_cert cert_term_sg false;
val cert_prop = gen_cert cert_prop_sg false;

fun cert_term_pats _ = map o gen_cert cert_term_sg true;
val cert_prop_pats = map o gen_cert cert_prop_sg true;


(* declare terms *)

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

fun map_defaults f = map_context (fn (thy, data, asms, binds, thms, cases, defs) =>
  (thy, data, asms, binds, thms, cases, f defs));

fun declare (ctxt as Context {asms = (_, (fixes, _)), ...}, t) =
  ctxt
  |> map_defaults (fn (types, sorts, used) => (ins_types (types, t), sorts, used))
  |> map_defaults (fn (types, sorts, used) => (types, ins_sorts (sorts, t), used))
  |> map_defaults (fn (types, sorts, used) => (types, sorts, ins_used (used, t)))
  |> map_defaults (fn (types, sorts, used) =>
      (ins_skolem (fn x => Vartab.lookup (types, (x, ~1))) (fixes, types), sorts, used));


fun declare_term t ctxt = declare (ctxt, t);
fun declare_terms ts ctxt = foldl declare (ctxt, ts);



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
      else warning ("Danger! Just introduced free type variable(s): " ^ commas tfrees ^ " in " ^
          space_implode " or " frees)
    end;

in

fun warn_extra_tfrees (ctxt1 as Context {defs = (_, _, used1), ...})
    (ctxt2 as Context {defs = (_, _, used2), ...}) = (warn_extra used1 used2; ctxt2);

end;


(* generalize type variables *)

fun gen_tfrees inner opt_outer =
  let
    val inner_used = used_table inner;
    val inner_fixes = fixed_names inner;
    val (outer_used, outer_fixes) =
      (case opt_outer of
        None => (Symtab.empty, [])
      | Some ctxt => (used_table ctxt, fixed_names ctxt));

    val extra_fixes = inner_fixes \\ outer_fixes;
    fun still_fixed (Free (x, _)) = not (x mem_string extra_fixes)
      | still_fixed _ = false;

    fun add (gen, (a, xs)) =
      if is_some (Symtab.lookup (outer_used, a)) orelse exists still_fixed xs
      then gen else a :: gen;
  in Symtab.foldl add ([], inner_used) end;

fun generalizeT inner outer =
  let
    val tfrees = gen_tfrees inner (Some outer);
    fun gen (x, S) = if x mem_string tfrees then TVar ((x, 0), S) else TFree (x, S);
  in Term.map_type_tfree gen end;

val generalize = Term.map_term_types oo generalizeT;


(* export theorems *)

fun get_free x (None, t as Free (y, _)) = if x = y then Some t else None
  | get_free _ (opt, _) = opt;

fun find_free t x = foldl_aterms (get_free x) (None, t);


local

fun export tfrees fixes casms thm =
  let
    val rule =
      thm
      |> Drule.forall_elim_vars 0
      |> Drule.implies_intr_list casms;
    val {sign, prop, ...} = Thm.rep_thm rule;
    val frees = map (Thm.cterm_of sign) (mapfilter (find_free prop) fixes);
  in
    rule
    |> Drule.forall_intr_list frees
    |> Drule.forall_elim_vars 0
    |> Drule.tvars_intr_list tfrees
  end;

fun diff_context inner None = (gen_tfrees inner None, fixed_names inner, assumptions inner)
  | diff_context inner (Some outer) =
      (gen_tfrees inner (Some outer),
        fixed_names inner \\ fixed_names outer,
        Library.drop (length (assumptions outer), assumptions inner));

in

fun export_wrt inner opt_outer =
  let
    val (tfrees, fixes, asms) = diff_context inner opt_outer;
    val casms = map (Drule.mk_cgoal o #1) asms;
    val tacs = map #2 asms;
  in (export tfrees fixes casms, tacs) end;

end;



(** bindings **)

(* update_binds *)

fun del_bind (ctxt, xi) =
  ctxt
  |> map_context (fn (thy, data, asms, binds, thms, cases, defs) =>
      (thy, data, asms, Vartab.update ((xi, None), binds), thms, cases, defs));

fun upd_bind (ctxt, ((x, i), t)) =
  let
    val T = Term.fastype_of t;
    val t' =
      if null (Term.term_tvars t \\ Term.typ_tvars T) then t
      else Var ((x ^ "_has_extra_type_vars_on_rhs", i), T);
  in
    ctxt
    |> declare_term t'
    |> map_context (fn (thy, data, asms, binds, thms, cases, defs) =>
        (thy, data, asms, Vartab.update (((x, i), Some (t', T)), binds), thms, cases, defs))
  end;

fun del_upd_bind (ctxt, (xi, None)) = del_bind (ctxt, xi)
  | del_upd_bind (ctxt, (xi, Some t)) = upd_bind (ctxt, (xi, t));

fun update_binds bs ctxt = foldl upd_bind (ctxt, bs);
fun delete_update_binds bs ctxt = foldl del_upd_bind (ctxt, bs);


(* simult_matches *)

fun simult_matches ctxt [] = []
  | simult_matches ctxt pairs =
      let
        val maxidx = foldl (fn (i, (t1, t2)) =>
          Int.max (i, Int.max (Term.maxidx_of_term t1, Term.maxidx_of_term t2))) (~1, pairs);
        val envs = Unify.smash_unifiers (sign_of ctxt, Envir.empty maxidx, pairs);
        val env =
          (case Seq.pull envs of
            None => raise CONTEXT ("Pattern match failed!", ctxt)      (* FIXME improve msg (!?) *)
          | Some (env, _) => env);
        val binds =
          (*Note: Envir.norm_term ensures proper type instantiation*)
          map (apsnd (Envir.norm_term env)) (Envir.alist_of env);
      in binds end;


(* add_binds(_i) *)

local

fun gen_bind prep (ctxt, (xi as (x, _), raw_t)) =
  ctxt |> delete_update_binds [(xi, apsome (prep ctxt) raw_t)];

fun gen_binds prep binds ctxt = foldl (gen_bind prep) (ctxt, binds);

in

val add_binds = gen_binds read_term;
val add_binds_i = gen_binds cert_term;

val auto_bind_goal = add_binds_i o AutoBind.goal;
val auto_bind_facts = add_binds_i oo AutoBind.facts;

end;


(* match_bind(_i) *)

local

fun prep_bind (prep, prep_pats) (ctxt, (raw_pats, raw_t)) =
  let
    val t = prep ctxt raw_t;
    val ctxt' = declare_term t ctxt;
    val pats = prep_pats (fastype_of t) ctxt' raw_pats;
    val binds = simult_matches ctxt' (map (rpair t) pats);
  in (ctxt', binds) end;

fun gen_binds prepp gen raw_binds ctxt =
  let
    val (ctxt', binds) = apsnd flat (foldl_map (prep_bind prepp) (ctxt, raw_binds));
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

val match_bind = gen_binds (read_term, read_term_pats);
val match_bind_i = gen_binds (cert_term, cert_term_pats);

end;


(* proposition patterns *)

fun prep_propp prep_prop prep_pats (ctxt, (raw_prop, (raw_pats1, raw_pats2))) =
  let
    val prop = prep_prop ctxt raw_prop;
    val ctxt' = declare_term prop ctxt;

    val pats = prep_pats ctxt' (raw_pats1 @ raw_pats2);    (*simultaneous type inference!*)
    val len1 = length raw_pats1;
  in (ctxt', (prop, (take (len1, pats), drop (len1, pats)))) end;

val read_propp = prep_propp read_prop read_prop_pats;
val cert_propp = prep_propp cert_prop cert_prop_pats;


fun gen_bind_propp prepp (ctxt, propp) =
  let
    val (ctxt', (prop, (pats1, pats2))) = prepp (ctxt, propp);
    val pairs =
      map (rpair prop) pats1 @
      map (rpair (Logic.strip_imp_concl prop)) pats2;   (* FIXME handle params!? *)
    val binds = simult_matches ctxt' pairs;

    (*note: context evaluated now, binds added later (lazy)*)
    val gen = generalize ctxt' ctxt;
    fun gen_binds ct = ct |> add_binds_i (map (apsnd (Some o gen)) binds);
  in (ctxt' |> add_binds_i (map (apsnd Some) binds), (prop, gen_binds)) end;

val bind_propp = gen_bind_propp read_propp;
val bind_propp_i = gen_bind_propp cert_propp;



(** theorems **)

(* get_thm(s) *)

fun get_thm (ctxt as Context {thy, thms, ...}) name =
  (case Symtab.lookup (thms, name) of
    Some (Some [th]) => th
  | Some (Some _) => raise CONTEXT ("Single theorem expected: " ^ quote name, ctxt)
  | _ => (PureThy.get_thm thy name handle THEORY (msg, _) => raise CONTEXT (msg, ctxt)));

fun get_thms (ctxt as Context {thy, thms, ...}) name =
  (case Symtab.lookup (thms, name) of
    Some (Some ths) => ths
  | _ => (PureThy.get_thms thy name handle THEORY (msg, _) => raise CONTEXT (msg, ctxt)));

fun get_thmss ctxt names = flat (map (get_thms ctxt) names);


(* put_thm(s) *)

fun put_thms ("", _) = I
  | put_thms (name, ths) = map_context
      (fn (thy, data, asms, binds, thms, cases, defs) =>
        (thy, data, asms, binds, Symtab.update ((name, Some ths), thms), cases, defs));

fun put_thm (name, th) = put_thms (name, [th]);

fun put_thmss [] ctxt = ctxt
  | put_thmss (th :: ths) ctxt = ctxt |> put_thms th |> put_thmss ths;


(* reset_thms *)

fun reset_thms name = map_context (fn (thy, data, asms, binds, thms, cases, defs) =>
  (thy, data, asms, binds, Symtab.update ((name, None), thms), cases, defs));


(* have_thmss *)

fun have_thmss more_ths name more_attrs ths_attrs ctxt =
  let
    fun app ((ct, ths), (th, attrs)) =
      let val (ct', th') = Thm.applys_attributes ((ct, th), attrs @ more_attrs)
      in (ct', th' :: ths) end
    val (ctxt', rev_thms) = foldl app ((ctxt, []), ths_attrs);
    val thms = flat (rev rev_thms) @ more_ths;
  in (ctxt' |> put_thms (name, thms), (name, thms)) end;



(** assumptions **)

(* assume *)

local

fun gen_assm prepp tac (ctxt, (name, attrs, raw_prop_pats)) =
  let
    val (ctxt', props) = foldl_map prepp (ctxt, raw_prop_pats);

    val cprops = map (Thm.cterm_of (sign_of ctxt')) props;
    val cprops_tac = map (rpair tac) cprops;
    val asms = map (Drule.forall_elim_vars 0 o Drule.assume_goal) cprops;

    val ths = map (fn th => ([th], [])) asms;
    val (ctxt'', (_, thms)) =
      ctxt'
      |> auto_bind_facts name props
      |> have_thmss [] name (attrs @ [Drule.tag_assumption]) ths;

    val ctxt''' =
      ctxt''
      |> map_context (fn (thy, data, ((asms_ct, asms_th), fixes), binds, thms, cases, defs) =>
        (thy, data, ((asms_ct @ cprops_tac, asms_th @ [(name, asms)]), fixes),
          binds, thms, cases, defs));
  in (ctxt''', (name, thms)) end;

fun gen_assms prepp tac args ctxt =
  let val (ctxt', thmss) = foldl_map (gen_assm prepp tac) (ctxt, args)
  in (warn_extra_tfrees ctxt ctxt', (thmss, prems_of ctxt')) end;

in

val assume = gen_assms (apsnd #1 o bind_propp);
val assume_i = gen_assms (apsnd #1 o bind_propp_i);

end;


(* variables *)

fun prep_vars prep_typ check (ctxt, (xs, raw_T)) =
  let
    val _ = (case filter (not o Syntax.is_identifier) (map (check_skolem ctxt check) xs) of
      [] => () | bads => raise CONTEXT ("Bad variable name(s): " ^ commas_quote bads, ctxt));

    val opt_T = apsome (prep_typ ctxt) raw_T;
    val T = if_none opt_T TypeInfer.logicT;
    val ctxt' = ctxt |> declare_terms (map (fn x => Free (x, T)) xs);
  in (ctxt', (xs, opt_T)) end;

val read_vars = prep_vars read_typ true;
val cert_vars = prep_vars cert_typ false;


(* fix *)

local

fun add_vars xs (fixes, names) =
  let
    val xs' = variantlist (xs, names);
    val fixes' = (xs ~~ map Syntax.skolem xs') @ fixes;
    val names' = xs' @ names;
  in (fixes', names') end;

fun map_vars f = map_context (fn (thy, data, (assumes, vars), binds, thms, cases, defs) =>
  (thy, data, (assumes, f vars), binds, thms, cases, defs));

fun gen_fix prep raw_vars ctxt =
  let
    val (ctxt', varss) = foldl_map prep (ctxt, raw_vars);
    val xs = flat (map fst varss);
  in
    (case Library.duplicates xs of
      [] => ()
    | dups => raise CONTEXT ("Duplicate variable name(s): " ^ commas_quote dups, ctxt));
    ctxt' |> map_vars (add_vars xs)
  end;

in

val fix = gen_fix read_vars;
val fix_i = gen_fix cert_vars;

end;



(** cases **)

fun check_case ctxt name (xs, ts) =
  if null (foldr Term.add_typ_tvars (map snd xs, [])) andalso
    null (foldr Term.add_term_vars (ts, [])) then ()
  else raise CONTEXT ("Illegal schematic variable(s) in case " ^ quote name, ctxt);

fun get_case (ctxt as Context {cases, ...}) name =
  (case assoc (cases, name) of
    None => raise CONTEXT ("Unknown case: " ^ quote name, ctxt)
  | Some c => (check_case ctxt name c; c));


fun add_cases xs = map_context (fn (thy, data, asms, binds, thms, cases, defs) =>
  (thy, data, asms, binds, thms, rev (filter_out (equal "" o #1) xs) @ cases, defs));



(** theory setup **)

val setup = [ProofDataData.init];


end;
