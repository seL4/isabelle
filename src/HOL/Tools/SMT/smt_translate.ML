(*  Title:      HOL/Tools/SMT/smt_translate.ML
    Author:     Sascha Boehme, TU Muenchen

Translate theorems into an SMT intermediate format and serialize them.
*)

signature SMT_TRANSLATE =
sig
  (*intermediate term structure*)
  datatype squant = SForall | SExists
  datatype 'a spattern = SPat of 'a list | SNoPat of 'a list
  datatype sterm =
    SVar of int |
    SApp of string * sterm list |
    SLet of string * sterm * sterm |
    SQua of squant * string list * sterm spattern list * int option * sterm

  (*translation configuration*)
  type prefixes = {sort_prefix: string, func_prefix: string}
  type sign = {
    header: string list,
    sorts: string list,
    dtyps: (string * (string * (string * string) list) list) list list,
    funcs: (string * (string list * string)) list }
  type config = {
    prefixes: prefixes,
    header: term list -> string list,
    is_fol: bool,
    has_datatypes: bool,
    serialize: string list -> sign -> sterm list -> string }
  type recon = {
    context: Proof.context,
    typs: typ Symtab.table,
    terms: term Symtab.table,
    rewrite_rules: thm list,
    assms: (int * thm) list }

  (*translation*)
  val add_config: SMT_Utils.class * (Proof.context -> config) ->
    Context.generic -> Context.generic 
  val translate: Proof.context -> string list -> (int * thm) list ->
    string * recon
end

structure SMT_Translate: SMT_TRANSLATE =
struct


(* intermediate term structure *)

datatype squant = SForall | SExists

datatype 'a spattern = SPat of 'a list | SNoPat of 'a list

datatype sterm =
  SVar of int |
  SApp of string * sterm list |
  SLet of string * sterm * sterm |
  SQua of squant * string list * sterm spattern list * int option * sterm



(* translation configuration *)

type prefixes = {sort_prefix: string, func_prefix: string}

type sign = {
  header: string list,
  sorts: string list,
  dtyps: (string * (string * (string * string) list) list) list list,
  funcs: (string * (string list * string)) list }

type config = {
  prefixes: prefixes,
  header: term list -> string list,
  is_fol: bool,
  has_datatypes: bool,
  serialize: string list -> sign -> sterm list -> string }

type recon = {
  context: Proof.context,
  typs: typ Symtab.table,
  terms: term Symtab.table,
  rewrite_rules: thm list,
  assms: (int * thm) list }



(* translation context *)

fun make_tr_context {sort_prefix, func_prefix} =
  (sort_prefix, 1, Typtab.empty, func_prefix, 1, Termtab.empty)

fun string_of_index pre i = pre ^ string_of_int i

fun add_typ T proper (cx as (sp, Tidx, typs, fp, idx, terms)) =
  (case Typtab.lookup typs T of
    SOME (n, _) => (n, cx)
  | NONE =>
      let
        val n = string_of_index sp Tidx
        val typs' = Typtab.update (T, (n, proper)) typs
      in (n, (sp, Tidx+1, typs', fp, idx, terms)) end)

fun add_fun t sort (cx as (sp, Tidx, typs, fp, idx, terms)) =
  (case Termtab.lookup terms t of
    SOME (n, _) => (n, cx)
  | NONE => 
      let
        val n = string_of_index fp idx
        val terms' = Termtab.update (t, (n, sort)) terms
      in (n, (sp, Tidx, typs, fp, idx+1, terms')) end)

fun sign_of header dtyps (_, _, typs, _, _, terms) = {
  header = header,
  sorts = Typtab.fold (fn (_, (n, true)) => cons n | _ => I) typs [],
  dtyps = dtyps,
  funcs = Termtab.fold (fn (_, (n, SOME ss)) => cons (n,ss) | _ => I) terms []}

fun recon_of ctxt rules thms ithms (_, _, typs, _, _, terms) =
  let
    fun add_typ (T, (n, _)) = Symtab.update (n, T)
    val typs' = Typtab.fold add_typ typs Symtab.empty

    fun add_fun (t, (n, _)) = Symtab.update (n, t)
    val terms' = Termtab.fold add_fun terms Symtab.empty

    val assms = map (pair ~1) thms @ ithms
  in
    {context=ctxt, typs=typs', terms=terms', rewrite_rules=rules, assms=assms}
  end



(* preprocessing *)

(** datatype declarations **)

fun collect_datatypes_and_records (tr_context, ctxt) ts =
  let
    val (declss, ctxt') =
      fold (Term.fold_types SMT_Datatypes.add_decls) ts ([], ctxt)

    fun is_decl_typ T = exists (exists (equal T o fst)) declss

    fun add_typ' T proper =
      (case SMT_Builtin.dest_builtin_typ ctxt' T of
        SOME n => pair n
      | NONE => add_typ T proper)

    fun tr_select sel =
      let val T = Term.range_type (Term.fastype_of sel)
      in add_fun sel NONE ##>> add_typ' T (not (is_decl_typ T)) end
    fun tr_constr (constr, selects) =
      add_fun constr NONE ##>> fold_map tr_select selects
    fun tr_typ (T, cases) = add_typ' T false ##>> fold_map tr_constr cases
    val (declss', tr_context') = fold_map (fold_map tr_typ) declss tr_context

    fun add (constr, selects) =
      Termtab.update (constr, length selects) #>
      fold (Termtab.update o rpair 1) selects
    val funcs = fold (fold (fold add o snd)) declss Termtab.empty
  in ((funcs, declss', tr_context', ctxt'), ts) end
    (* FIXME: also return necessary datatype and record theorems *)


(** eta-expand quantifiers, let expressions and built-ins *)

local
  fun eta f T t = Abs (Name.uu, T, f (Term.incr_boundvars 1 t $ Bound 0))

  fun exp f T = eta f (Term.domain_type (Term.domain_type T))

  fun exp2 T q =
    let val U = Term.domain_type T
    in Abs (Name.uu, U, q $ eta I (Term.domain_type U) (Bound 0)) end

  fun exp2' T l =
    let val (U1, U2) = Term.dest_funT T ||> Term.domain_type
    in Abs (Name.uu, U1, eta I U2 (l $ Bound 0)) end

  fun expf k i T t =
    let val Ts = drop i (fst (SMT_Utils.dest_funT k T))
    in
      Term.incr_boundvars (length Ts) t
      |> fold_rev (fn i => fn u => u $ Bound i) (0 upto length Ts - 1)
      |> fold_rev (fn T => fn u => Abs (Name.uu, T, u)) Ts
    end
in

fun eta_expand ctxt is_fol funcs =
  let
    fun exp_func t T ts =
      (case Termtab.lookup funcs t of
        SOME k =>
          Term.list_comb (t, ts)
          |> k <> length ts ? expf k (length ts) T
      | NONE => Term.list_comb (t, ts))

    fun expand ((q as Const (@{const_name All}, _)) $ Abs a) = q $ abs_expand a
      | expand ((q as Const (@{const_name All}, T)) $ t) = q $ exp expand T t
      | expand (q as Const (@{const_name All}, T)) = exp2 T q
      | expand ((q as Const (@{const_name Ex}, _)) $ Abs a) = q $ abs_expand a
      | expand ((q as Const (@{const_name Ex}, T)) $ t) = q $ exp expand T t
      | expand (q as Const (@{const_name Ex}, T)) = exp2 T q
      | expand ((l as Const (@{const_name Let}, _)) $ t $ Abs a) =
          if is_fol then expand (Term.betapply (Abs a, t))
          else l $ expand t $ abs_expand a
      | expand ((l as Const (@{const_name Let}, T)) $ t $ u) =
          if is_fol then expand (u $ t)
          else l $ expand t $ exp expand (Term.range_type T) u
      | expand ((l as Const (@{const_name Let}, T)) $ t) =
          if is_fol then
            let val U = Term.domain_type (Term.range_type T)
            in Abs (Name.uu, U, Bound 0 $ Term.incr_boundvars 1 t) end
          else exp2 T (l $ expand t)
      | expand (l as Const (@{const_name Let}, T)) =
          if is_fol then 
            let val U = Term.domain_type (Term.range_type T)
            in
              Abs (Name.uu, Term.domain_type T, Abs (Name.uu, U,
                Bound 0 $ Bound 1))
            end
          else exp2' T l
      | expand t =
          (case Term.strip_comb t of
            (u as Const (c as (_, T)), ts) =>
              (case SMT_Builtin.dest_builtin ctxt c ts of
                SOME (_, k, us, mk) =>
                  if k = length us then mk (map expand us)
                  else if k < length us then
                    chop k (map expand us) |>> mk |> Term.list_comb
                  else expf k (length ts) T (mk (map expand us))
              | NONE => exp_func u T (map expand ts))
          | (u as Free (_, T), ts) => exp_func u T (map expand ts)
          | (Abs a, ts) => Term.list_comb (abs_expand a, map expand ts)
          | (u, ts) => Term.list_comb (u, map expand ts))

    and abs_expand (n, T, t) = Abs (n, T, expand t)
  
  in map expand end

end


(** introduce explicit applications **)

local
  (*
    Make application explicit for functions with varying number of arguments.
  *)

  fun add t i = apfst (Termtab.map_default (t, i) (Integer.min i))
  fun add_type T = apsnd (Typtab.update (T, ()))

  fun min_arities t =
    (case Term.strip_comb t of
      (u as Const _, ts) => add u (length ts) #> fold min_arities ts
    | (u as Free _, ts) => add u (length ts) #> fold min_arities ts
    | (Abs (_, T, u), ts) => add_type T #> min_arities u #> fold min_arities ts
    | (_, ts) => fold min_arities ts)

  fun minimize types t i =
    let
      fun find_min j [] _ = j
        | find_min j (U :: Us) T =
            if Typtab.defined types T then j
            else find_min (j + 1) Us (U --> T)

      val (Ts, T) = Term.strip_type (Term.type_of t)
    in find_min 0 (take i (rev Ts)) T end

  fun app u (t, T) =
    (Const (@{const_name SMT.fun_app}, T --> T) $ t $ u, Term.range_type T)

  fun apply i t T ts =
    let
      val (ts1, ts2) = chop i ts
      val (_, U) = SMT_Utils.dest_funT i T
    in fst (fold app ts2 (Term.list_comb (t, ts1), U)) end
in

fun intro_explicit_application ctxt funcs ts =
  let
    val (arities, types) = fold min_arities ts (Termtab.empty, Typtab.empty)
    val arities' = Termtab.map (minimize types) arities

    fun app_func t T ts =
      if is_some (Termtab.lookup funcs t) then Term.list_comb (t, ts)
      else apply (the (Termtab.lookup arities' t)) t T ts

    fun in_list T f t = HOLogic.mk_list T (map f (HOLogic.dest_list t))

    fun traverse Ts t =
      (case Term.strip_comb t of
        (q as Const (@{const_name All}, _), [Abs (x, T, u)]) =>
          q $ Abs (x, T, in_trigger (T :: Ts) u)
      | (q as Const (@{const_name Ex}, _), [Abs (x, T, u)]) =>
          q $ Abs (x, T, in_trigger (T :: Ts) u)
      | (q as Const (@{const_name Let}, _), [u1, u2 as Abs _]) =>
          q $ traverse Ts u1 $ traverse Ts u2
      | (u as Const (c as (_, T)), ts) =>
          (case SMT_Builtin.dest_builtin ctxt c ts of
            SOME (_, k, us, mk) =>
              let
                val (ts1, ts2) = chop k (map (traverse Ts) us)
                val U = Term.strip_type T |>> snd o chop k |> (op --->)
              in apply 0 (mk ts1) U ts2 end
          | NONE => app_func u T (map (traverse Ts) ts))
      | (u as Free (_, T), ts) => app_func u T (map (traverse Ts) ts)
      | (u as Bound i, ts) => apply 0 u (nth Ts i) (map (traverse Ts) ts)
      | (Abs (n, T, u), ts) => traverses Ts (Abs (n, T, traverse (T::Ts) u)) ts
      | (u, ts) => traverses Ts u ts)
    and in_trigger Ts ((c as @{const SMT.trigger}) $ p $ t) =
          c $ in_pats Ts p $ in_weight Ts t
      | in_trigger Ts t = in_weight Ts t
    and in_pats Ts ps =
      in_list @{typ "SMT.pattern list"}
        (in_list @{typ SMT.pattern} (in_pat Ts)) ps
    and in_pat Ts ((p as Const (@{const_name SMT.pat}, _)) $ t) =
          p $ traverse Ts t
      | in_pat Ts ((p as Const (@{const_name SMT.nopat}, _)) $ t) =
          p $ traverse Ts t
      | in_pat _ t = raise TERM ("bad pattern", [t])
    and in_weight Ts ((c as @{const SMT.weight}) $ w $ t) =
          c $ w $ traverse Ts t
      | in_weight Ts t = traverse Ts t 
    and traverses Ts t ts = Term.list_comb (t, map (traverse Ts) ts)
  in map (traverse []) ts end

val fun_app_eq = mk_meta_eq @{thm SMT.fun_app_def}

end


(** map HOL formulas to FOL formulas (i.e., separate formulas froms terms) **)

local
  val term_bool = @{lemma "SMT.term_true ~= SMT.term_false"
    by (simp add: SMT.term_true_def SMT.term_false_def)}

  val is_quant = member (op =) [@{const_name All}, @{const_name Ex}]

  val fol_rules = [
    Let_def,
    mk_meta_eq @{thm SMT.term_true_def},
    mk_meta_eq @{thm SMT.term_false_def},
    @{lemma "P = True == P" by (rule eq_reflection) simp},
    @{lemma "if P then True else False == P" by (rule eq_reflection) simp}]

  fun as_term t = @{const HOL.eq (bool)} $ t $ @{const SMT.term_true}

  exception BAD_PATTERN of unit

  fun wrap_in_if pat t =
    if pat then
      raise BAD_PATTERN ()
    else
      @{const If (bool)} $ t $ @{const SMT.term_true} $ @{const SMT.term_false}

  fun is_builtin_conn_or_pred ctxt c ts =
    is_some (SMT_Builtin.dest_builtin_conn ctxt c ts) orelse
    is_some (SMT_Builtin.dest_builtin_pred ctxt c ts)

  fun builtin b ctxt c ts =
    (case (Const c, ts) of
      (@{const HOL.eq (bool)}, [t, u]) =>
        if t = @{const SMT.term_true} orelse u = @{const SMT.term_true} then
          SMT_Builtin.dest_builtin_eq ctxt t u
        else b ctxt c ts
    | _ => b ctxt c ts)
in

fun folify ctxt =
  let
    fun in_list T f t = HOLogic.mk_list T (map_filter f (HOLogic.dest_list t))

    fun in_term pat t =
      (case Term.strip_comb t of
        (@{const True}, []) => @{const SMT.term_true}
      | (@{const False}, []) => @{const SMT.term_false}
      | (u as Const (@{const_name If}, _), [t1, t2, t3]) =>
          if pat then raise BAD_PATTERN ()
          else u $ in_form t1 $ in_term pat t2 $ in_term pat t3
      | (Const (c as (n, _)), ts) =>
          if is_builtin_conn_or_pred ctxt c ts then wrap_in_if pat (in_form t)
          else if is_quant n then wrap_in_if pat (in_form t)
          else Term.list_comb (Const c, map (in_term pat) ts)
      | (Free c, ts) => Term.list_comb (Free c, map (in_term pat) ts)
      | _ => t)

    and in_weight ((c as @{const SMT.weight}) $ w $ t) = c $ w $ in_form t
      | in_weight t = in_form t 

    and in_pat ((p as Const (@{const_name SMT.pat}, _)) $ t) =
          p $ in_term true t
      | in_pat ((p as Const (@{const_name SMT.nopat}, _)) $ t) =
          p $ in_term true t
      | in_pat t = raise TERM ("bad pattern", [t])

    and in_pats ps =
      in_list @{typ "SMT.pattern list"}
        (SOME o in_list @{typ SMT.pattern} (try in_pat)) ps

    and in_trigger ((c as @{const SMT.trigger}) $ p $ t) =
          c $ in_pats p $ in_weight t
      | in_trigger t = in_weight t

    and in_form t =
      (case Term.strip_comb t of
        (q as Const (qn, _), [Abs (n, T, u)]) =>
          if is_quant qn then q $ Abs (n, T, in_trigger u)
          else as_term (in_term false t)
      | (Const c, ts) =>
          (case SMT_Builtin.dest_builtin_conn ctxt c ts of
            SOME (_, _, us, mk) => mk (map in_form us)
          | NONE =>
              (case SMT_Builtin.dest_builtin_pred ctxt c ts of
                SOME (_, _, us, mk) => mk (map (in_term false) us)
              | NONE => as_term (in_term false t)))
      | _ => as_term (in_term false t))
  in
    map in_form #>
    cons (SMT_Utils.prop_of term_bool) #>
    pair (fol_rules, [term_bool], builtin)
  end

end


(* translation into intermediate format *)

(** utility functions **)

val quantifier = (fn
    @{const_name All} => SOME SForall
  | @{const_name Ex} => SOME SExists
  | _ => NONE)

fun group_quant qname Ts (t as Const (q, _) $ Abs (_, T, u)) =
      if q = qname then group_quant qname (T :: Ts) u else (Ts, t)
  | group_quant _ Ts t = (Ts, t)

fun dest_weight (@{const SMT.weight} $ w $ t) =
      (SOME (snd (HOLogic.dest_number w)), t)
  | dest_weight t = (NONE, t)

fun dest_pat (Const (@{const_name SMT.pat}, _) $ t) = (t, true)
  | dest_pat (Const (@{const_name SMT.nopat}, _) $ t) = (t, false)
  | dest_pat t = raise TERM ("bad pattern", [t])

fun dest_pats [] = I
  | dest_pats ts =
      (case map dest_pat ts |> split_list ||> distinct (op =) of
        (ps, [true]) => cons (SPat ps)
      | (ps, [false]) => cons (SNoPat ps)
      | _ => raise TERM ("bad multi-pattern", ts))

fun dest_trigger (@{const SMT.trigger} $ tl $ t) =
      (rev (fold (dest_pats o HOLogic.dest_list) (HOLogic.dest_list tl) []), t)
  | dest_trigger t = ([], t)

fun dest_quant qn T t = quantifier qn |> Option.map (fn q =>
  let
    val (Ts, u) = group_quant qn [T] t
    val (ps, p) = dest_trigger u
    val (w, b) = dest_weight p
  in (q, rev Ts, ps, w, b) end)

fun fold_map_pat f (SPat ts) = fold_map f ts #>> SPat
  | fold_map_pat f (SNoPat ts) = fold_map f ts #>> SNoPat


(** translation from Isabelle terms into SMT intermediate terms **)

fun intermediate header dtyps builtin ctxt ts trx =
  let
    fun transT (T as TFree _) = add_typ T true
      | transT (T as TVar _) = (fn _ => raise TYPE ("bad SMT type", [T], []))
      | transT (T as Type _) =
          (case SMT_Builtin.dest_builtin_typ ctxt T of
            SOME n => pair n
          | NONE => add_typ T true)

    fun app n ts = SApp (n, ts)

    fun trans t =
      (case Term.strip_comb t of
        (Const (qn, _), [Abs (_, T, t1)]) =>
          (case dest_quant qn T t1 of
            SOME (q, Ts, ps, w, b) =>
              fold_map transT Ts ##>> fold_map (fold_map_pat trans) ps ##>>
              trans b #>> (fn ((Ts', ps'), b') => SQua (q, Ts', ps', w, b'))
          | NONE => raise TERM ("unsupported quantifier", [t]))
      | (Const (@{const_name Let}, _), [t1, Abs (_, T, t2)]) =>
          transT T ##>> trans t1 ##>> trans t2 #>>
          (fn ((U, u1), u2) => SLet (U, u1, u2))
      | (u as Const (c as (_, T)), ts) =>
          (case builtin ctxt c ts of
            SOME (n, _, us, _) => fold_map trans us #>> app n
          | NONE => transs u T ts)
      | (u as Free (_, T), ts) => transs u T ts
      | (Bound i, []) => pair (SVar i)
      | _ => raise TERM ("bad SMT term", [t]))
 
    and transs t T ts =
      let val (Us, U) = SMT_Utils.dest_funT (length ts) T
      in
        fold_map transT Us ##>> transT U #-> (fn Up =>
        add_fun t (SOME Up) ##>> fold_map trans ts #>> SApp)
      end

    val (us, trx') = fold_map trans ts trx
  in ((sign_of (header ts) dtyps trx', us), trx') end



(* translation *)

structure Configs = Generic_Data
(
  type T = (Proof.context -> config) SMT_Utils.dict
  val empty = []
  val extend = I
  fun merge data = SMT_Utils.dict_merge fst data
)

fun add_config (cs, cfg) = Configs.map (SMT_Utils.dict_update (cs, cfg))

fun get_config ctxt = 
  let val cs = SMT_Config.solver_class_of ctxt
  in
    (case SMT_Utils.dict_get (Configs.get (Context.Proof ctxt)) cs of
      SOME cfg => cfg ctxt
    | NONE => error ("SMT: no translation configuration found " ^
        "for solver class " ^ quote (SMT_Utils.string_of_class cs)))
  end

fun translate ctxt comments ithms =
  let
    val {prefixes, is_fol, header, has_datatypes, serialize} = get_config ctxt

    val with_datatypes =
      has_datatypes andalso Config.get ctxt SMT_Config.datatypes

    fun no_dtyps (tr_context, ctxt) ts =
      ((Termtab.empty, [], tr_context, ctxt), ts)

    val ts1 = map (Envir.beta_eta_contract o SMT_Utils.prop_of o snd) ithms

    val ((funcs, dtyps, tr_context, ctxt1), ts2) =
      ((make_tr_context prefixes, ctxt), ts1)
      |-> (if with_datatypes then collect_datatypes_and_records else no_dtyps)

    fun is_binder (Const (@{const_name Let}, _) $ _) = true
      | is_binder t = Lambda_Lifting.is_quantifier t

    fun mk_trigger ((q as Const (@{const_name All}, _)) $ Abs (n, T, t)) =
          q $ Abs (n, T, mk_trigger t)
      | mk_trigger (eq as (Const (@{const_name HOL.eq}, T) $ lhs $ _)) =
          Term.domain_type T --> @{typ SMT.pattern}
          |> (fn T => Const (@{const_name SMT.pat}, T) $ lhs)
          |> HOLogic.mk_list @{typ SMT.pattern} o single
          |> HOLogic.mk_list @{typ "SMT.pattern list"} o single
          |> (fn t => @{const SMT.trigger} $ t $ eq)
      | mk_trigger t = t

    val (ctxt2, ts3) =
      ts2
      |> eta_expand ctxt1 is_fol funcs
      |> rpair ctxt1
      |-> Lambda_Lifting.lift_lambdas NONE is_binder
      |-> (fn (ts', defs) => fn ctxt' =>
          map mk_trigger defs @ ts'
          |> intro_explicit_application ctxt' funcs 
          |> pair ctxt')

    val ((rewrite_rules, extra_thms, builtin), ts4) =
      (if is_fol then folify ctxt2 else pair ([], [], I)) ts3

    val rewrite_rules' = fun_app_eq :: rewrite_rules
  in
    (ts4, tr_context)
    |-> intermediate header dtyps (builtin SMT_Builtin.dest_builtin) ctxt2
    |>> uncurry (serialize comments)
    ||> recon_of ctxt2 rewrite_rules' extra_thms ithms
  end

end
