(*  Title:      Pure/Isar/proof_context.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Proof context information.

TODO:
  - pretty_bind: use syntax (!?) (show_types etc.);
  - smash_unifiers: ever invents new vars (???);
*)

(* FIXME tmp *)
val proof_debug = ref false;

signature PROOF_CONTEXT =
sig
  type context
  exception CONTEXT of string * context
  val theory_of: context -> theory
  val sign_of: context -> Sign.sg
  val print_binds: context -> unit
  val print_thms: context -> unit
  val print_context: context -> unit
  val print_proof_data: theory -> unit
  val init_context: theory -> context
  val read_typ: context -> string -> typ
  val cert_typ: context -> typ -> typ
  val read_term: context -> string -> term
  val read_prop: context -> string -> term
  val read_pat: context -> string -> term
  val cert_term: context -> term -> term
  val cert_prop: context -> term -> term
  val declare_term: term -> context -> context
  val declare_terms: term list -> context -> context
  val add_binds: (indexname * string) list -> context -> context
  val add_binds_i: (indexname * term) list -> context -> context
  val match_binds: (string * string) list -> context -> context
  val match_binds_i: (term * term) list -> context -> context
  val thms_closure: context -> xstring -> tthm list option
  val get_tthm: context -> string -> tthm
  val get_tthms: context -> string -> tthm list
  val get_tthmss: context -> string list -> tthm list
  val put_tthm: string * tthm -> context -> context
  val put_tthms: string * tthm list -> context -> context
  val put_tthmss: (string * tthm list) list -> context -> context
  val have_tthms: string -> context attribute list
    -> (tthm * context attribute list) list -> context -> context * (string * tthm list)
  val assumptions: context -> tthm list
  val fixed_names: context -> string list
  val assume: string -> context attribute list -> string list -> context
    -> context * (string * tthm list)
  val assume_i: string -> context attribute list -> term list -> context
    -> context * (string * tthm list)
  val fix: (string * string option) list -> context -> context
  val fix_i: (string * typ) list -> context -> context
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
   {thy: theory,                                (*current theory*)
    data: Object.T Symtab.table,                (*user data*)
    asms:
      (string * tthm list) list *               (*assumes: A ==> _*)
      ((string * string) list * string list),   (*fixes: !!x. _*)
    binds: (term * typ) Vartab.table,           (*term bindings*)
    thms: tthm list Symtab.table,               (*local thms*)
    defs:
      typ Vartab.table *                        (*type constraints*)
      sort Vartab.table *                       (*default sorts*)
      int *					(*maxidx*)
      string list};                             (*used type variable names*)

exception CONTEXT of string * context;


fun make_context (thy, data, asms, binds, thms, defs) =
  Context {thy = thy, data = data, asms = asms, binds = binds, thms = thms, defs = defs};

fun map_context f (Context {thy, data, asms, binds, thms, defs}) =
  make_context (f (thy, data, asms, binds, thms, defs));

fun theory_of (Context {thy, ...}) = thy;
val sign_of = Theory.sign_of o theory_of;



(** print context information **)

(* FIXME tmp*)
fun debug f x = if ! proof_debug then f x else ();

fun print_items prt name items =
  let
    fun pretty_itms (name, [x]) = Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1, prt x]
      | pretty_itms (name, xs) = Pretty.big_list (name ^ ":") (map prt xs);
  in Pretty.writeln (Pretty.big_list name (map pretty_itms items)) end;


(* term bindings *)

fun print_binds (Context {thy, binds, ...}) =
  let
    val prt_term = Sign.pretty_term (Theory.sign_of thy);

    fun fix_var (x, i) =
      (case try Syntax.dest_binding x of
        None => Syntax.string_of_vname (x, i)
      | Some x' => if i = 0 then "??" ^ x' else Syntax.string_of_vname (x, i));
    fun pretty_bind (xi, (t, T)) = Pretty.block
      [Pretty.str (fix_var xi), Pretty.str " ==", Pretty.brk 1, prt_term t];
  in Pretty.writeln (Pretty.big_list "Term bindings:" (map pretty_bind (Vartab.dest binds))) end;


(* local theorems *)

fun print_thms (Context {thms, ...}) =
  print_items Attribute.pretty_tthm "Local theorems:" (Symtab.dest thms);


(* main context *)

fun print_context (ctxt as Context {thy, data = _, asms = (assumes, (fixes, _)), binds = _,
    thms = _, defs = (types, sorts, maxidx, used)}) =
  let
    val sign = Theory.sign_of thy;

    val term_of_tthm = #prop o Thm.rep_thm o Attribute.thm_of;
    val prt_term = Sign.pretty_term sign;
    val prt_typ = Sign.pretty_typ sign;
    val prt_sort = Sign.pretty_sort sign;

    (*theory*)
    val pretty_thy = Pretty.block [Pretty.str "Theory:", Pretty.brk 1, Sign.pretty_sg sign];

    (*fixes*)
    fun prt_fix (x, x') = Pretty.str (x ^ " = " ^ x');

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
    debug Pretty.writeln pretty_thy;
    Pretty.writeln (Pretty.big_list "Fixed variables:" (map prt_fix (rev fixes)));
    print_items (prt_term o term_of_tthm) "Assumptions:" assumes;
    debug print_binds ctxt;
    debug print_thms ctxt;
    debug Pretty.writeln (Pretty.big_list "Type constraints:" (map prt_defT (Vartab.dest types)));
    debug Pretty.writeln (Pretty.big_list "Default sorts:" (map prt_defS (Vartab.dest sorts)));
    debug writeln ("Maxidx: " ^ string_of_int maxidx);
    debug Pretty.writeln (Pretty.strs ("Used type variable names:" :: used))
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

fun init_context thy =
  let val data = Symtab.map (fn (_, (init, _)) => init thy) (ProofDataData.get thy) in
    make_context (thy, data, ([], ([], [])), Vartab.empty, Symtab.empty,
      (Vartab.empty, Vartab.empty, ~1, []))
  end;



(** prepare types **)

fun read_typ (ctxt as Context {defs = (_, sorts, _, _), ...}) s =
  let
    val sign = sign_of ctxt;
    fun def_sort xi = Vartab.lookup (sorts, xi);
  in
    transform_error (Sign.read_typ (sign, def_sort)) s
      handle ERROR_MESSAGE msg => raise CONTEXT (msg, ctxt)
  end;

fun cert_typ ctxt raw_T =
  Sign.certify_typ (sign_of ctxt) raw_T
    handle TYPE (msg, _, _) => raise CONTEXT (msg, ctxt);



(** prepare terms and propositions **)

(*
  (1) read / certify wrt. signature of context
  (2) intern Skolem constants
  (3) expand term bindings
*)


(* read / certify wrt. signature *)     (*exception ERROR*) (*exception TERM*)

fun read_def_termT sg (types, sorts, used) (s, T) =
  Thm.term_of (#1 (Thm.read_def_cterm (sg, types, sorts) used true (s, T)));

fun read_term_sg sg (defs as (_, _, used)) s =
  read_def_termT sg defs (s, TVar ((variant used "'z", 0), logicS));

fun read_prop_sg sg defs s = read_def_termT sg defs (s, propT);


fun cert_term_sg sg t = Thm.term_of (Thm.cterm_of sg t);

fun cert_prop_sg sg tm =
  let
    val ctm = Thm.cterm_of sg tm;
    val {t, T, ...} = Thm.rep_cterm ctm;
  in
    if T = propT then t
    else raise TERM ("Term not of type prop", [t])
  end;


(* intern_skolem *)

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


(* norm_term *)

(*beta normal form for terms (not eta normal form), chase variables in
  bindings environment (code taken from Pure/envir.ML)*)

fun norm_term (ctxt as Context {binds, ...}) =
  let
    (*raised when norm has no effect on a term, to do sharing instead of copying*)
    exception SAME;

    fun norm (t as Var (xi, T)) =
          (case Vartab.lookup (binds, xi) of
            Some (u, U) =>
              if T = U then (norm u handle SAME => u)
              else raise TYPE ("norm_term: ill-typed variable assigment", [T, U], [t, u])
          | None =>
              if can Syntax.dest_binding (#1 xi) then
                raise CONTEXT ("Unbound binding: " ^ Syntax.string_of_vname xi, ctxt)
              else raise SAME)
      | norm (Abs (a, T, body)) =  Abs (a, T, norm body)
      | norm (Abs (_, _, body) $ t) = normh (subst_bound (t, body))
      | norm (f $ t) =
          ((case norm f of
            Abs (_, _, body) => normh (subst_bound (t, body))
          | nf => nf $ (norm t handle SAME => t)) handle SAME => f $ norm t)
      | norm _ =  raise SAME
    and normh t = norm t handle SAME => t
  in normh end;


(* read terms *)

fun gen_read read is_pat (ctxt as Context {binds, defs = (types, sorts, _, used), ...}) s =
  let
    val sign = sign_of ctxt;

    fun def_type xi =
      (case Vartab.lookup (types, xi) of
        None => if is_pat then None else apsome #2 (Vartab.lookup (binds, xi))
      | some => some);

    fun def_sort xi = Vartab.lookup (sorts, xi);
  in
    (transform_error (read sign (def_type, def_sort, used)) s
      handle TERM (msg, _) => raise CONTEXT (msg, ctxt)
      | ERROR_MESSAGE msg => raise CONTEXT (msg, ctxt))
    |> intern_skolem ctxt true
    |> (if is_pat then I else norm_term ctxt)
  end;

val read_term = gen_read read_term_sg false;
val read_prop = gen_read read_prop_sg false;
val read_pat = gen_read read_term_sg true;


(* certify terms *)

fun gen_cert cert is_pat ctxt t =
  (cert (sign_of ctxt) t handle TERM (msg, _) => raise CONTEXT (msg, ctxt))
  |> intern_skolem ctxt false
  |> (if is_pat then I else norm_term ctxt);

val cert_term = gen_cert cert_term_sg false;
val cert_prop = gen_cert cert_prop_sg false;
val cert_pat = gen_cert cert_term_sg true;


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

fun map_defaults f = map_context
  (fn (thy, data, asms, binds, thms, defs) => (thy, data, asms, binds, thms, f defs));

fun declare (ctxt, t) =
  ctxt
  |> map_defaults (fn (types, sorts, maxidx, used) => (ins_types (types, t), sorts, maxidx, used))
  |> map_defaults (fn (types, sorts, maxidx, used) => (types, ins_sorts (sorts, t), maxidx, used))
  |> map_defaults (fn (types, sorts, maxidx, used) => (types, sorts, maxidx, ins_used (used, t)))
  |> map_defaults (fn (types, sorts, maxidx, used) =>
      (types, sorts, Int.max (maxidx, Term.maxidx_of_term t), used));


fun declare_term t ctxt = declare (ctxt, t);
fun declare_terms ts ctxt = foldl declare (ctxt, ts);

fun prep_declare prep (ctxt, s) =
  let val t = prep ctxt s
  in (ctxt |> declare_term t, t) end;



(** bindings **)

(* update_binds *)

fun upd_bind (ctxt, (xi, t)) =
  let val T = fastype_of t in
    ctxt
    |> declare_term t
    |> map_context (fn (thy, data, asms, binds, thms, defs) =>
        (thy, data, asms, Vartab.update ((xi, (t, T)), binds), thms, defs))
  end;

fun update_binds bs ctxt = foldl upd_bind (ctxt, bs);
fun update_binds_env env = update_binds (Envir.alist_of env);


(* add_binds(_i) -- sequential *)

fun gen_bind prep (ctxt, (xi as (x, _), raw_t)) =
  let val t = prep ctxt raw_t in
    if can Syntax.dest_binding x then ctxt |> update_binds [(xi, t)]
    else raise CONTEXT ("Illegal variable name for term binding: " ^
      quote (Syntax.string_of_vname xi), ctxt)
  end;

fun gen_binds prep binds ctxt = foldl (gen_bind prep) (ctxt, binds);

val add_binds = gen_binds read_term;
val add_binds_i = gen_binds cert_term;


(* match_binds(_i) -- parallel *)

fun prep_pair prep_pat prep (ctxt, (raw_pat, raw_t)) =
  let
    val pat = prep_pat ctxt raw_pat;
    val (ctxt', t) = prep_declare prep (ctxt, raw_t);
  in (ctxt', (pat, t)) end;

fun gen_match_binds prep_pat prep raw_pairs ctxt =
  let
    val (ctxt', pairs) = foldl_map (prep_pair prep_pat prep) (ctxt, raw_pairs);
    val Context {defs = (_, _, maxidx, _), ...} = ctxt';
    val envs = Unify.smash_unifiers (sign_of ctxt', Envir.empty maxidx, pairs);
    val env =
      (case Seq.pull envs of
        None => raise CONTEXT ("Pattern match failed!", ctxt')
      | Some (env, _) => env);
  in ctxt' |> update_binds_env env end;

val match_binds = gen_match_binds read_pat read_term;
val match_binds_i = gen_match_binds cert_pat cert_term;



(** theorems **)

(* thms_closure *)

fun thms_closure (Context {thy, thms, ...}) =
  let
    val global_closure = PureThy.thms_closure thy;
    fun get name =
      (case global_closure name of
        None => Symtab.lookup (thms, name)
      | some => some);
  in get end;


(* get_tthm(s) *)

fun get_tthm (ctxt as Context {thy, thms, ...}) name =
  (case Symtab.lookup (thms, name) of
    Some [th] => th
  | Some _ => raise CONTEXT ("Single theorem expected: " ^ quote name, ctxt)
  | None => (PureThy.get_tthm thy name handle THEORY (msg, _) => raise CONTEXT (msg, ctxt)));

fun get_tthms (ctxt as Context {thy, thms, ...}) name =
  (case Symtab.lookup (thms, name) of
    Some ths => ths
  | None => (PureThy.get_tthms thy name handle THEORY (msg, _) => raise CONTEXT (msg, ctxt)));

fun get_tthmss ctxt names = flat (map (get_tthms ctxt) names);


(* put_tthm(s) *)

fun put_tthms (name, ths) = map_context
  (fn (thy, data, asms, binds, thms, defs) =>
    (thy, data, asms, binds, Symtab.update ((name, ths), thms), defs));

fun put_tthm (name, th) = put_tthms (name, [th]);

fun put_tthmss [] ctxt = ctxt
  | put_tthmss (th :: ths) ctxt = ctxt |> put_tthms th |> put_tthmss ths;


(* have_tthms *)

fun have_tthms name more_attrs ths_attrs ctxt =
  let
    fun app ((ct, ths), (th, attrs)) =
      let val (ct', th') = Attribute.apply ((ct, th), attrs @ more_attrs)
      in (ct', th' :: ths) end
    val (ctxt', rev_thms) = foldl app ((ctxt, []), ths_attrs);
    val thms = rev rev_thms;
  in (ctxt' |> put_tthms (name, thms), (name, thms)) end;



(** assumptions **)

(* get assumptions *)

fun assumptions (Context {asms = (asms, _), ...}) = flat (map #2 asms);
fun fixed_names (Context {asms = (_, (fixes, _)), ...}) = map #2 fixes;


(* assume *)

fun gen_assume prep name attrs raw_props ctxt =
  let
    val (ctxt', props) = foldl_map prep (ctxt, raw_props);
    val sign = sign_of ctxt';
    val ths = map (fn t => ((Thm.assume (Thm.cterm_of sign t), []), [])) props;

    val (ctxt'', (_, tthms)) =
      ctxt'
      |> have_tthms name (Attribute.tag_assumption :: attrs) ths

    val ctxt''' =
      ctxt''
      |> map_context (fn (thy, data, (assumes, fixes), binds, thms, defs) =>
        (thy, data, (assumes @ [(name, tthms)], fixes), binds, thms, defs));
  in (ctxt''', (name, tthms)) end;

val assume = gen_assume (prep_declare read_prop);
val assume_i = gen_assume (prep_declare cert_prop);


(* fix *)

fun read_skolemT (Context {defs = (_, _, _, used), ...}) None = Type.param used ("'z", logicS)
  | read_skolemT ctxt (Some s) = read_typ ctxt s;

fun gen_fix prep check (ctxt, (x, raw_T)) =
  ctxt
  |> declare_term (Free (check_skolem ctxt check x, prep ctxt raw_T))
  |> map_context (fn (thy, data, (assumes, (fixes, names)), binds, thms, defs) =>
      let val x' = variant names x in
        (thy, data, (assumes, ((x, Syntax.skolem x') :: fixes, x' :: names)), binds, thms, defs)
      end);

fun gen_fixs prep check xs ctxt = foldl (gen_fix prep check) (ctxt, xs);


val fix = gen_fixs read_skolemT true;
val fix_i = gen_fixs cert_typ false;



(** theory setup **)

val setup = [ProofDataData.init];


end;
