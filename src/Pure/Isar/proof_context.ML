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
  val strings_of_prems: context -> string list
  val strings_of_context: context -> string list
  val print_proof_data: theory -> unit
  val init: theory -> context
  val read_typ: context -> string -> typ
  val cert_typ: context -> typ -> typ
  val cert_skolem: context -> string -> string
  val read_termTs: context -> (string * typ) list -> term list * (indexname * typ) list
  val read_term: context -> string -> term
  val read_prop: context -> string -> term
  val read_term_pat: context -> string -> term
  val read_prop_pat: context -> string -> term
  val cert_term: context -> term -> term
  val cert_prop: context -> term -> term
  val declare_term: term -> context -> context
  val declare_terms: term list -> context -> context
  val warn_extra_tfrees: context -> context -> context
  val add_binds: (indexname * string option) list -> context -> context
  val add_binds_i: (indexname * term option) list -> context -> context
  val auto_bind_goal: term -> context -> context
  val auto_bind_facts: string -> term list -> context -> context
  val match_binds: (string list * string) list -> context -> context
  val match_binds_i: (term list * term) list -> context -> context
  val bind_propp: string * (string list * string list) -> context -> context * term
  val bind_propp_i: term * (term list * term list) -> context -> context * term
  val get_thm: context -> string -> thm
  val get_thms: context -> string -> thm list
  val get_thmss: context -> string list -> thm list
  val put_thm: string * thm -> context -> context
  val put_thms: string * thm list -> context -> context
  val put_thmss: (string * thm list) list -> context -> context
  val reset_thms: string -> context -> context
  val have_thmss: thm list -> string -> context attribute list
    -> (thm list * context attribute list) list -> context -> context * (string * thm list)
  val assumptions: context -> (cterm * ((int -> tactic) * (int -> tactic))) list
  val fixed_names: context -> string list
  val assume: ((int -> tactic) * (int -> tactic))
    -> (string * context attribute list * (string * (string list * string list)) list) list
    -> context -> context * ((string * thm list) list * thm list)
  val assume_i: ((int -> tactic) * (int -> tactic))
    -> (string * context attribute list * (term * (term list * term list)) list) list
    -> context -> context * ((string * thm list) list * thm list)
  val fix: (string list * string option) list -> context -> context
  val fix_i: (string list * typ option) list -> context -> context
  val setup: (theory -> theory) list
end;

signature PROOF_CONTEXT_PRIVATE =
sig
  include PROOF_CONTEXT
  val init_data: Object.kind -> (theory -> Object.T) * (context -> Object.T -> unit)
    -> theory -> theory
  val print_data: Object.kind -> context -> unit
  val get_data: Object.kind -> (Object.T -> 'a) -> context -> 'a
  val put_data: Object.kind -> ('a -> Object.T) -> 'a -> context -> context
end;

structure ProofContext: PROOF_CONTEXT_PRIVATE =
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
    defs:
      typ Vartab.table *                                                (*type constraints*)
      sort Vartab.table *                                               (*default sorts*)
      string list};                                                     (*used type var names*)

exception CONTEXT of string * context;


fun make_context (thy, data, asms, binds, thms, defs) =
  Context {thy = thy, data = data, asms = asms, binds = binds, thms = thms, defs = defs};

fun map_context f (Context {thy, data, asms, binds, thms, defs}) =
  make_context (f (thy, data, asms, binds, thms, defs));

fun theory_of (Context {thy, ...}) = thy;
val sign_of = Theory.sign_of o theory_of;

fun prems_of (Context {asms = ((_, asms), _), ...}) = flat (map #2 asms);



(** print context information **)

val show_hyps = ref false;

fun pretty_thm thm =
  if ! show_hyps then setmp Display.show_hyps true Display.pretty_thm_no_quote thm
  else Display.pretty_cterm (#prop (Thm.crep_thm thm));

val verbose = ref false;
fun verb f x = if ! verbose then f x else [];
val verb_string = verb (Library.single o Pretty.string_of);

fun strings_of_items prt name items =
  let
    fun pretty_itms (name, [x]) = Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1, prt x]
      | pretty_itms (name, xs) = Pretty.big_list (name ^ ":") (map prt xs);
  in
    if null items andalso not (! verbose) then []
    else [Pretty.string_of (Pretty.big_list name (map pretty_itms items))]
  end;


(* term bindings *)

val smash_option = fn (_, None) => None | (xi, Some b) => Some (xi, b);

fun strings_of_binds (ctxt as Context {binds, ...}) =
  let
    val prt_term = Sign.pretty_term (sign_of ctxt);
    fun pretty_bind (xi, (t, T)) = prt_term (Logic.mk_equals (Var (xi, T), t));
    val bs = mapfilter smash_option (Vartab.dest binds);
  in
    if null bs andalso not (! verbose) then []
    else [Pretty.string_of (Pretty.big_list "term bindings:" (map pretty_bind bs))]
  end;

val print_binds = seq writeln o strings_of_binds;


(* local theorems *)

fun strings_of_thms (Context {thms, ...}) =
  strings_of_items pretty_thm "local theorems:" (mapfilter smash_option (Symtab.dest thms));

val print_thms = seq writeln o strings_of_thms;


(* main context *)

fun strings_of_prems ctxt =
  (case prems_of ctxt of
    [] => []
  | prems => [Pretty.string_of (Pretty.big_list "prems:" (map pretty_thm prems))]);

fun strings_of_context (ctxt as Context {asms = (_, (fixes, _)),
    defs = (types, sorts, used), ...}) =
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


    (* defaults *)

    fun prt_atom prt prtT (x, X) = Pretty.block
      [prt x, Pretty.str " ::", Pretty.brk 1, prtT X];

    fun prt_var (x, ~1) = prt_term (Syntax.free x)
      | prt_var xi = prt_term (Syntax.var xi);

    fun prt_varT (x, ~1) = prt_typ (TFree (x, []))
      | prt_varT xi = prt_typ (TVar (xi, []));

    val prt_defT = prt_atom prt_var prt_typ;
    val prt_defS = prt_atom prt_varT prt_sort;
  in
    verb_string pretty_thy @
    (if null fixes then [] else [Pretty.string_of (prt_fixes (rev fixes))]) @
    strings_of_prems ctxt @
    verb strings_of_binds ctxt @
    verb strings_of_thms ctxt @
    verb_string (Pretty.big_list "type constraints:" (map prt_defT (Vartab.dest types))) @
    verb_string (Pretty.big_list "default sorts:" (map prt_defS (Vartab.dest sorts))) @
    verb_string (Pretty.strs ("used type variable names:" :: used))
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
    ctxt |> map_context (fn (thy, data, asms, binds, thms, defs) =>
      (thy, Symtab.update ((Object.name_of_kind kind, f x), data), asms, binds, thms, defs)));


(* init context *)

fun init thy =
  let val data = Symtab.map (fn (_, (f, _)) => f thy) (ProofDataData.get thy) in
    make_context (thy, data, (([], []), ([], [])), Vartab.empty, Symtab.empty,
      (Vartab.empty, Vartab.empty, []))
  end;


(** default sorts and types **)

fun def_sort (Context {defs = (_, sorts, _), ...}) xi = Vartab.lookup (sorts, xi);

fun def_type (Context {binds, defs = (types, _, _), ...}) is_pat xi =
  (case Vartab.lookup (types, xi) of
    None =>
      if is_pat then None
      else (case Vartab.lookup (binds, xi) of Some (Some (_, T)) => Some T | _ => None)
  | some => some);



(** prepare types **)

fun read_typ ctxt s =
  transform_error (Sign.read_typ (sign_of ctxt, def_sort ctxt)) s
    handle ERROR_MESSAGE msg => raise CONTEXT (msg, ctxt);

fun cert_typ ctxt raw_T =
  Sign.certify_typ (sign_of ctxt) raw_T
    handle TYPE (msg, _, _) => raise CONTEXT (msg, ctxt);



(** prepare variables **)

fun prep_var prep_typ ctxt (x, T) =
  if not (Syntax.is_identifier x) then
    raise CONTEXT ("Bad variable name: " ^ quote x, ctxt)
  else (x, apsome (prep_typ ctxt) T);

val read_var = prep_var read_typ;
val cert_var = prep_var cert_typ;


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
  let val (cts, env) = Thm.read_def_cterms (sg, types, sorts) used freeze sTs
  in (map Thm.term_of cts, env) end;

fun read_def_termT freeze sg defs sT = apfst hd (read_def_termTs freeze sg defs [sT]);


fun read_term_sg freeze sg (defs as (_, _, used)) s =
  #1 (read_def_termT freeze sg defs (s, dummyT));

fun read_prop_sg freeze sg defs s =
  #1 (read_def_termT freeze sg defs (s, propT));


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

fun norm_term (ctxt as Context {binds, ...}) =
  let
    (*raised when norm has no effect on a term, to do sharing instead of copying*)
    exception SAME;

    fun norm (t as Var (xi, T)) =
          (case Vartab.lookup (binds, xi) of
            Some (Some (u, U)) =>
              if T = U then (norm u handle SAME => u)
              else raise TYPE ("norm_term: ill-typed variable assigment", [T, U], [t, u])
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

fun gen_read read app is_pat (ctxt as Context {defs = (_, _, used), ...}) s =
  (transform_error (read (sign_of ctxt) (def_type ctxt is_pat, def_sort ctxt, used)) s
    handle TERM (msg, _) => raise CONTEXT (msg, ctxt)
    | ERROR_MESSAGE msg => raise CONTEXT (msg, ctxt))
  |> app (intern_skolem ctxt true)
  |> app (if is_pat then I else norm_term ctxt)
  |> app (if is_pat then prepare_dummies else (reject_dummies ctxt));

val read_termTs = gen_read (read_def_termTs false) (apfst o map) false;
val read_term = gen_read (read_term_sg true) I false;
val read_prop = gen_read (read_prop_sg true) I false;
val read_term_pat = gen_read (read_term_sg false) I true;
val read_prop_pat = gen_read (read_prop_sg false) I true;


(* certify terms *)

fun gen_cert cert is_pat ctxt t =
  (cert (sign_of ctxt) t handle TERM (msg, _) => raise CONTEXT (msg, ctxt))
  |> intern_skolem ctxt false
  |> (if is_pat then I else norm_term ctxt);

val cert_term = gen_cert cert_term_sg false;
val cert_prop = gen_cert cert_prop_sg false;
val cert_term_pat = gen_cert cert_term_sg true;
val cert_prop_pat = gen_cert cert_prop_sg true;


(* declare terms *)

val ins_types = foldl_aterms
  (fn (types, Free (x, T)) => Vartab.update (((x, ~1), T), types)
    | (types, Var v) => Vartab.update (v, types)
    | (types, _) => types);

val ins_sorts = foldl_types (foldl_atyps
  (fn (sorts, TFree (x, S)) => Vartab.update (((x, ~1), S), sorts)
    | (sorts, TVar v) => Vartab.update (v, sorts)
    | (sorts, _) => sorts));

val ins_used = foldl_types (foldl_atyps
  (fn (used, TFree (x, _)) => x ins used
    | (used, TVar ((x, _), _)) => x ins used
    | (used, _) => used));

fun ins_skolem def_ty = foldr
  (fn ((x, x'), types) =>
    (case def_ty x' of
      Some T => Vartab.update (((x, ~1), T), types)
    | None => types));

fun map_defaults f = map_context
  (fn (thy, data, asms, binds, thms, defs) => (thy, data, asms, binds, thms, f defs));

fun declare (ctxt as Context {asms = (_, (fixes, _)), ...}, t) =
  ctxt
  |> map_defaults (fn (types, sorts, used) => (ins_types (types, t), sorts, used))
  |> map_defaults (fn (types, sorts, used) => (types, ins_sorts (sorts, t), used))
  |> map_defaults (fn (types, sorts, used) => (types, sorts, ins_used (used, t)))
  |> map_defaults (fn (types, sorts, used) =>
      (ins_skolem (fn x => Vartab.lookup (types, (x, ~1))) (fixes, types), sorts, used));


fun declare_term t ctxt = declare (ctxt, t);
fun declare_terms ts ctxt = foldl declare (ctxt, ts);


(* warn_extra_tfrees *)

fun warn_extra used1 used2 =
  if used1 = used2 then ()
  else
    (case Library.gen_rems (op =) (used2, used1) of
      [] => ()
    | extras => warning ("Introducing free type variables: " ^ commas (rev extras)));

fun warn_extra_tfrees (ctxt1 as Context {defs = (_, _, used1), ...})
    (ctxt2 as Context {defs = (_, _, used2), ...}) = (warn_extra used1 used2; ctxt2);



(** bindings **)

(* update_binds *)

fun del_bind (ctxt, xi) =
  ctxt
  |> map_context (fn (thy, data, asms, binds, thms, defs) =>
      (thy, data, asms, Vartab.update ((xi, None), binds), thms, defs));

fun upd_bind (ctxt, (xi, t)) =
  let val T = fastype_of t in
    ctxt
    |> declare_term t
    |> map_context (fn (thy, data, asms, binds, thms, defs) =>
        (thy, data, asms, Vartab.update ((xi, Some (t, T)), binds), thms, defs))
  end;

fun del_upd_bind (ctxt, (xi, None)) = del_bind (ctxt, xi)
  | del_upd_bind (ctxt, (xi, Some t)) = upd_bind (ctxt, (xi, t));

fun update_binds bs ctxt = foldl upd_bind (ctxt, bs);
fun update_binds_env env =      (*Note: Envir.norm_term ensures proper type instantiation*)
  update_binds (map (apsnd (Envir.norm_term env)) (Envir.alist_of env));

fun delete_update_binds bs ctxt = foldl del_upd_bind (ctxt, bs);


(* add_binds(_i) -- sequential *)

local

fun gen_bind prep (ctxt, (xi as (x, _), raw_t)) =
  ctxt |> delete_update_binds [(xi, apsome (prep ctxt) raw_t)];

fun gen_binds prep binds ctxt =
  warn_extra_tfrees ctxt (foldl (gen_bind prep) (ctxt, binds));

in

val add_binds = gen_binds read_term;
val add_binds_i = gen_binds cert_term;
val auto_bind_goal = add_binds_i o AutoBind.goal;
val auto_bind_facts = add_binds_i oo AutoBind.facts;

end;


(* match_binds(_i) -- parallel *)

fun prep_declare_match (prep_pat, prep) (ctxt, (raw_pats, raw_t)) =
  let
    val t = prep ctxt raw_t;
    val ctxt' = ctxt |> declare_term t;
    val matches = map (fn (f, raw_pat) => (prep_pat ctxt' raw_pat, f t)) raw_pats;
  in (ctxt', (matches, t)) end;

fun maxidx_of_pair (t1, t2) = Int.max (Term.maxidx_of_term t1, Term.maxidx_of_term t2);

fun gen_match_binds _ [] ctxt = ctxt
  | gen_match_binds prepp args ctxt =
      let
        val raw_pairs = map (apfst (map (pair I))) args;
        val (ctxt', matches) = foldl_map (prep_declare_match prepp) (ctxt, raw_pairs);
        val pairs = flat (map #1 matches);
        val maxidx = foldl (fn (i, p) => Int.max (i, maxidx_of_pair p)) (~1, pairs);
        val envs = Unify.smash_unifiers (sign_of ctxt', Envir.empty maxidx, pairs);
        val env =
          (case Seq.pull envs of
            None => raise CONTEXT ("Pattern match failed!", ctxt')
          | Some (env, _) => env);
      in ctxt' |> update_binds_env env |> warn_extra_tfrees ctxt end;

val match_binds = gen_match_binds (read_term_pat, read_term);
val match_binds_i = gen_match_binds (cert_term_pat, cert_term);


(* bind proposition patterns *)

fun gen_bind_propp prepp (raw_prop, (raw_pats1, raw_pats2)) ctxt =
  let
    val raw_pats = map (pair I) raw_pats1 @ map (pair Logic.strip_imp_concl) raw_pats2;
    val (ctxt', (pairs, prop)) = prep_declare_match prepp (ctxt, (raw_pats, raw_prop));
  in (ctxt' |> match_binds_i (map (apfst single) pairs), prop) end;

val bind_propp = gen_bind_propp (read_prop_pat, read_prop);
val bind_propp_i = gen_bind_propp (cert_prop_pat, cert_prop);



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
      (fn (thy, data, asms, binds, thms, defs) =>
        (thy, data, asms, binds, Symtab.update ((name, Some ths), thms), defs));

fun put_thm (name, th) = put_thms (name, [th]);

fun put_thmss [] ctxt = ctxt
  | put_thmss (th :: ths) ctxt = ctxt |> put_thms th |> put_thmss ths;


(* reset_thms *)

fun reset_thms name = map_context (fn (thy, data, asms, binds, thms, defs) =>
  (thy, data, asms, binds, Symtab.update ((name, None), thms), defs));


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

(* get assumptions *)

fun assumptions (Context {asms = ((asms, _), _), ...}) = asms;
fun fixed_names (Context {asms = (_, (fixes, _)), ...}) = map #2 fixes;


(* assume *)

local

fun gen_assm prepp tac (ctxt, (name, attrs, raw_prop_pats)) =
  let
    val (ctxt', props) = foldl_map (fn (c, x) => prepp x c) (ctxt, raw_prop_pats);

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
      |> map_context (fn (thy, data, ((asms_ct, asms_th), fixes), binds, thms, defs) =>
        (thy, data, ((asms_ct @ cprops_tac, asms_th @ [(name, asms)]), fixes), binds, thms, defs));
  in (ctxt''', (name, thms)) end;

fun gen_assms prepp tac args ctxt =
  let val (ctxt', thmss) = foldl_map (gen_assm prepp tac) (ctxt, args)
  in (warn_extra_tfrees ctxt ctxt', (thmss, prems_of ctxt')) end;

in

val assume = gen_assms bind_propp;
val assume_i = gen_assms bind_propp_i;

end;


(* fix *)

fun gen_fix prep_var check (ctxt, (x, raw_T)) =
  (check_skolem ctxt check x;
    ctxt
    |> (case snd (prep_var ctxt (x, raw_T)) of None => I | Some T => declare_term (Free (x, T)))
    |> map_context (fn (thy, data, (assumes, (fixes, names)), binds, thms, defs) =>
      let val x' = variant names x in
        (thy, data, (assumes, ((x, Syntax.skolem x') :: fixes, x' :: names)), binds, thms, defs)
      end));

fun dist_vars ctxt (xs, T) =
  (case Library.duplicates xs of
    [] => map (rpair T) xs
  | dups => raise CONTEXT ("Duplicate variable names in declaration: " ^ commas_quote dups, ctxt));

fun gen_fixs prep check vars ctxt =
  foldl (gen_fix prep check) (ctxt, flat (map (dist_vars ctxt) vars));

val fix = gen_fixs read_var true;
val fix_i = gen_fixs cert_var false;



(** theory setup **)

val setup = [ProofDataData.init];


end;
