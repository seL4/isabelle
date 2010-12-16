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

structure U = SMT_Utils
structure B = SMT_Builtin


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

fun recon_of ctxt rules thms ithms revertT revert (_, _, typs, _, _, terms) =
  let
    fun add_typ (T, (n, _)) = Symtab.update (n, revertT T)
    val typs' = Typtab.fold add_typ typs Symtab.empty

    fun add_fun (t, (n, _)) = Symtab.update (n, revert t)
    val terms' = Termtab.fold add_fun terms Symtab.empty

    val assms = map (pair ~1) thms @ ithms
  in
    {context=ctxt, typs=typs', terms=terms', rewrite_rules=rules, assms=assms}
  end



(* preprocessing *)

(** mark built-in constants as Var **)

fun mark_builtins ctxt =
  let
    (*
      Note: schematic terms cannot occur anymore in terms at this stage.
    *)
    fun mark t =
      (case Term.strip_comb t of
        (u as Const (@{const_name If}, _), ts) => marks u ts
      | (u as @{const SMT.weight}, [t1, t2]) =>
          mark t2 #>> (fn t2' => u $ t1 $ t2')
      | (u as Const c, ts) =>
          (case B.builtin_num ctxt t of
            SOME (n, T) =>
              let val v = ((n, 0), T)
              in Vartab.update v #> pair (Var v) end
          | NONE =>
              (case B.builtin_fun ctxt c ts of
                SOME ((ni, T), us, U) =>
                  Vartab.update (ni, U) #> marks (Var (ni, T)) us
              | NONE => marks u ts))
      | (Abs (n, T, u), ts) => mark u #-> (fn u' => marks (Abs (n, T, u')) ts)
      | (u, ts) => marks u ts)
 
    and marks t ts = fold_map mark ts #>> Term.list_comb o pair t

  in (fn ts => swap (fold_map mark ts Vartab.empty)) end

fun mark_builtins' ctxt t = hd (snd (mark_builtins ctxt [t]))


(** FIXME **)

local
  (*
    mark constructors and selectors as Vars (forcing eta-expansion),
    add missing datatype selectors via hypothetical definitions,
    also return necessary datatype and record theorems
  *)
in

fun collect_datatypes_and_records (tr_context, ctxt) ts =
  (([], tr_context, ctxt), ts)

end


(** eta-expand quantifiers, let expressions and built-ins *)

local
  fun eta T t = Abs (Name.uu, T, Term.incr_boundvars 1 t $ Bound 0)

  fun exp T = eta (Term.domain_type (Term.domain_type T))

  fun exp2 T q =
    let val U = Term.domain_type T
    in Abs (Name.uu, U, q $ eta (Term.domain_type U) (Bound 0)) end

  fun exp2' T l =
    let val (U1, U2) = Term.dest_funT T ||> Term.domain_type
    in Abs (Name.uu, U1, eta U2 (l $ Bound 0)) end

  fun expf t i T ts =
    let val Ts = U.dest_funT i T |> fst |> drop (length ts)
    in Term.list_comb (t, ts) |> fold_rev eta Ts end

  fun expand ((q as Const (@{const_name All}, _)) $ Abs a) = q $ abs_expand a
    | expand ((q as Const (@{const_name All}, T)) $ t) = q $ exp T t
    | expand (q as Const (@{const_name All}, T)) = exp2 T q
    | expand ((q as Const (@{const_name Ex}, _)) $ Abs a) = q $ abs_expand a
    | expand ((q as Const (@{const_name Ex}, T)) $ t) = q $ exp T t
    | expand (q as Const (@{const_name Ex}, T)) = exp2 T q
    | expand ((l as Const (@{const_name Let}, _)) $ t $ Abs a) =
        l $ expand t $ abs_expand a
    | expand ((l as Const (@{const_name Let}, T)) $ t $ u) =
        l $ expand t $ exp (Term.range_type T) u
    | expand ((l as Const (@{const_name Let}, T)) $ t) = exp2 T (l $ expand t)
    | expand (l as Const (@{const_name Let}, T)) = exp2' T l
    | expand (Abs a) = abs_expand a
    | expand t =
        (case Term.strip_comb t of
          (u as Const (@{const_name If}, T), ts) => expf u 3 T (map expand ts)
        | (u as Var ((_, i), T), ts) => expf u i T (map expand ts)
        | (u, ts) => Term.list_comb (u, map expand ts))

  and abs_expand (n, T, t) = Abs (n, T, expand t)
in

val eta_expand = map expand

end


(** lambda-lifting **)

local
  fun mk_def Ts T lhs rhs =
    let
      val eq = HOLogic.eq_const T $ lhs $ rhs
      val trigger =
        [[Const (@{const_name SMT.pat}, T --> @{typ SMT.pattern}) $ lhs]]
        |> map (HOLogic.mk_list @{typ SMT.pattern})
        |> HOLogic.mk_list @{typ "SMT.pattern list"}
      fun mk_all T t = HOLogic.all_const T $ Abs (Name.uu, T, t)
    in fold mk_all Ts (@{const SMT.trigger} $ trigger $ eq) end

  fun replace_lambda Us Ts t (cx as (defs, ctxt)) =
    let
      val T = Term.fastype_of1 (Us @ Ts, t)
      val lev = length Us
      val bs = sort int_ord (Term.add_loose_bnos (t, lev, []))
      val bss = map_index (fn (i, j) => (j, Integer.add lev i)) bs
      val norm = perhaps (AList.lookup (op =) bss)
      val t' = Term.map_aterms (fn Bound i => Bound (norm i) | t => t) t
      val Ts' = map (nth Ts) bs

      fun mk_abs U u = Abs (Name.uu, U, u)
      val abs_rhs = fold mk_abs Ts' (fold mk_abs Us t')
    in
      (case Termtab.lookup defs abs_rhs of
        SOME (f, _) => (Term.list_comb (f, map Bound bs), cx)
      | NONE =>
          let
            val (n, ctxt') =
              yield_singleton Variable.variant_fixes Name.uu ctxt
            val f = Free (n, rev Ts' ---> (rev Us ---> T))
            fun mk_bapp i t = t $ Bound i
            val lhs =
              f
              |> fold_rev (mk_bapp o snd) bss
              |> fold_rev mk_bapp (0 upto (length Us - 1))
            val def = mk_def (Us @ Ts') T lhs t'
          in (f, (Termtab.update (abs_rhs, (f, def)) defs, ctxt')) end)
    end

  fun dest_abs Ts (Abs (_, T, t)) = dest_abs (T :: Ts) t
    | dest_abs Ts t = (Ts, t)

  fun traverse Ts t =
    (case t of
      (q as Const (@{const_name All}, _)) $ Abs a =>
        abs_traverse Ts a #>> (fn a' => q $ Abs a')
    | (q as Const (@{const_name Ex}, _)) $ Abs a =>
        abs_traverse Ts a #>> (fn a' => q $ Abs a')
    | (l as Const (@{const_name Let}, _)) $ u $ Abs a =>
        traverse Ts u ##>> abs_traverse Ts a #>>
        (fn (u', a') => l $ u' $ Abs a')
    | Abs _ =>
        let val (Us, u) = dest_abs [] t
        in traverse (Us @ Ts) u #-> replace_lambda Us Ts end
    | u1 $ u2 => traverse Ts u1 ##>> traverse Ts u2 #>> (op $)
    | _ => pair t)

  and abs_traverse Ts (n, T, t) = traverse (T::Ts) t #>> (fn t' => (n, T, t'))
in

fun lift_lambdas ctxt ts =
  (Termtab.empty, ctxt)
  |> fold_map (traverse []) ts
  |> (fn (us, (defs, ctxt')) =>
       (ctxt', Termtab.fold (cons o snd o snd) defs us))

end


(** introduce explicit applications **)

local
  (*
    Make application explicit for functions with varying number of arguments.
  *)

  fun add t ts =
    Termtab.map_default (t, []) (Ord_List.insert int_ord (length ts))

  fun collect t =
    (case Term.strip_comb t of
      (u as Const _, ts) => add u ts #> fold collect ts
    | (u as Free _, ts) => add u ts #> fold collect ts
    | (Abs (_, _, u), ts) => collect u #> fold collect ts
    | (_, ts) => fold collect ts)

  fun app ts (t, T) =
    let val f = Const (@{const_name SMT.fun_app}, T --> T)
    in (Term.list_comb (f $ t, ts), snd (U.dest_funT (length ts) T)) end 

  fun appl _ _ [] = fst
    | appl _ [] ts = fst o app ts
    | appl i (k :: ks) ts =
        let val (ts1, ts2) = chop (k - i) ts
        in appl k ks ts2 o app ts1 end

  fun appl0 [_] ts (t, _) = Term.list_comb (t, ts)
    | appl0 (0 :: ks) ts tT = appl 0 ks ts tT
    | appl0 ks ts tT = appl 0 ks ts tT

  fun apply terms T t ts = appl0 (Termtab.lookup_list terms t) ts (t, T)

  fun get_arities i t =
    (case Term.strip_comb t of
      (Bound j, ts) =>
        (if i = j then Ord_List.insert int_ord (length ts) else I) #>
        fold (get_arities i) ts
    | (Abs (_, _, u), ts) => get_arities (i+1) u #> fold (get_arities i) ts
    | (_, ts) => fold (get_arities i) ts)
in

fun intro_explicit_application ts =
  let
    val terms = fold collect ts Termtab.empty

    fun traverse (env as (arities, Ts)) t =
      (case Term.strip_comb t of
        (u as Const (_, T), ts) => apply terms T u (map (traverse env) ts)
      | (u as Free (_, T), ts) => apply terms T u (map (traverse env) ts)
      | (u as Bound i, ts) =>
          appl0 (nth arities i) (map (traverse env) ts) (u, nth Ts i)
      | (Abs (n, T, u), ts) =>
          let val env' = (get_arities 0 u [] :: arities, T :: Ts)
          in traverses env (Abs (n, T, traverse env' u)) ts end
      | (u, ts) => traverses env u ts)
    and traverses env t ts = Term.list_comb (t, map (traverse env) ts)
  in map (traverse ([], [])) ts end

val fun_app_eq = mk_meta_eq @{thm SMT.fun_app_def}

end


(** map HOL formulas to FOL formulas (i.e., separate formulas froms terms) **)

val tboolT = @{typ SMT.term_bool}
val term_true = Const (@{const_name True}, tboolT)
val term_false = Const (@{const_name False}, tboolT)

val term_bool = @{lemma "True ~= False" by simp}
val term_bool_prop =
  let
    fun replace @{const HOL.eq (bool)} = @{const HOL.eq (SMT.term_bool)}
      | replace @{const True} = term_true
      | replace @{const False} = term_false
      | replace t = t
  in Term.map_aterms replace (U.prop_of term_bool) end

val fol_rules = [
  Let_def,
  @{lemma "P = True == P" by (rule eq_reflection) simp},
  @{lemma "if P then True else False == P" by (rule eq_reflection) simp}]

fun reduce_let (Const (@{const_name Let}, _) $ t $ u) =
      reduce_let (Term.betapply (u, t))
  | reduce_let (t $ u) = reduce_let t $ reduce_let u
  | reduce_let (Abs (n, T, t)) = Abs (n, T, reduce_let t)
  | reduce_let t = t

fun is_pred_type NONE = false
  | is_pred_type (SOME T) = (Term.body_type T = @{typ bool})

fun is_conn_type NONE = false
  | is_conn_type (SOME T) =
      forall (equal @{typ bool}) (Term.body_type T :: Term.binder_types T)

fun revert_typ @{typ SMT.term_bool} = @{typ bool}
  | revert_typ (Type (n, Ts)) = Type (n, map revert_typ Ts)
  | revert_typ T = T

val revert_types = Term.map_types revert_typ

fun folify ctxt builtins =
  let
    fun as_term t = @{const HOL.eq (SMT.term_bool)} $ t $ term_true

    fun as_tbool @{typ bool} = tboolT
      | as_tbool (Type (n, Ts)) = Type (n, map as_tbool Ts)
      | as_tbool T = T
    fun mapTs f g i = U.dest_funT i #> (fn (Ts, T) => map f Ts ---> g T)
    fun predT i = mapTs as_tbool I i
    fun funcT i = mapTs as_tbool as_tbool i
    fun func i (n, T) = (n, funcT i T)

    fun map_ifT T = T |> Term.dest_funT ||> funcT 2 |> (op -->)
    val if_term = @{const If (bool)} |> Term.dest_Const ||> map_ifT |> Const
    fun wrap_in_if t = if_term $ t $ term_true $ term_false

    fun in_list T f t = HOLogic.mk_list T (map f (HOLogic.dest_list t))

    fun in_term t =
      (case Term.strip_comb t of
        (Const (n as @{const_name If}, T), [t1, t2, t3]) =>
          Const (n, map_ifT T) $ in_form t1 $ in_term t2 $ in_term t3
      | (Const (@{const_name HOL.eq}, _), _) => wrap_in_if (in_form t)
      | (Var (ni as (_, i), T), ts) =>
          let val U = Vartab.lookup builtins ni
          in
            if is_conn_type U orelse is_pred_type U then wrap_in_if (in_form t)
            else Term.list_comb (Var (ni, funcT i T), map in_term ts)
          end
      | (Const c, ts) =>
          Term.list_comb (Const (func (length ts) c), map in_term ts)
      | (Free c, ts) =>
          Term.list_comb (Free (func (length ts) c), map in_term ts)
      | _ => t)

    and in_weight ((c as @{const SMT.weight}) $ w $ t) = c $ w $ in_form t
      | in_weight t = in_form t 

    and in_pat (Const (c as (@{const_name pat}, _)) $ t) =
          Const (func 1 c) $ in_term t
      | in_pat (Const (c as (@{const_name nopat}, _)) $ t) =
          Const (func 1 c) $ in_term t
      | in_pat t = raise TERM ("bad pattern", [t])

    and in_pats ps =
      in_list @{typ "pattern list"} (in_list @{typ pattern} in_pat) ps

    and in_trig ((c as @{const trigger}) $ p $ t) = c $ in_pats p $ in_weight t
      | in_trig t = in_weight t

    and in_form t =
      (case Term.strip_comb t of
        (q as Const (qn, _), [Abs (n, T, u)]) =>
          if member (op =) [@{const_name All}, @{const_name Ex}] qn then
            q $ Abs (n, as_tbool T, in_trig u)
          else as_term (in_term t)
      | (u as Const (@{const_name If}, _), ts) =>
          Term.list_comb (u, map in_form ts)
      | (b as @{const HOL.eq (bool)}, ts) => Term.list_comb (b, map in_form ts)
      | (Const (n as @{const_name HOL.eq}, T), ts) =>
          Term.list_comb (Const (n, predT 2 T), map in_term ts)
      | (b as Var (ni as (_, i), T), ts) =>
          if is_conn_type (Vartab.lookup builtins ni) then
            Term.list_comb (b, map in_form ts)
          else if is_pred_type (Vartab.lookup builtins ni) then
            Term.list_comb (Var (ni, predT i T), map in_term ts)
          else as_term (in_term t)
      | _ => as_term (in_term t))
  in
    map (reduce_let #> in_form) #>
    cons (mark_builtins' ctxt term_bool_prop) #>
    pair (fol_rules, [term_bool])
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

fun dest_pat (Const (@{const_name pat}, _) $ t) = (t, true)
  | dest_pat (Const (@{const_name nopat}, _) $ t) = (t, false)
  | dest_pat t = raise TERM ("bad pattern", [t])

fun dest_pats [] = I
  | dest_pats ts =
      (case map dest_pat ts |> split_list ||> distinct (op =) of
        (ps, [true]) => cons (SPat ps)
      | (ps, [false]) => cons (SNoPat ps)
      | _ => raise TERM ("bad multi-pattern", ts))

fun dest_trigger (@{const trigger} $ tl $ t) =
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

fun intermediate header dtyps ctxt ts trx =
  let
    fun transT (T as TFree _) = add_typ T true
      | transT (T as TVar _) = (fn _ => raise TYPE ("bad SMT type", [T], []))
      | transT (T as Type _) =
          (case B.builtin_typ ctxt T of
            SOME n => pair n
          | NONE => add_typ T true)

    val unmarked_builtins = [@{const_name If}, @{const_name HOL.eq}]

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
      | (Var ((n, _), _), ts) => fold_map trans ts #>> app n
      | (u as Const (c as (n, T)), ts) =>
          if member (op =) unmarked_builtins n then
            (case B.builtin_fun ctxt c ts of
              SOME (((m, _), _), us, _) => fold_map trans us #>> app m
            | NONE => raise TERM ("not a built-in symbol", [t]))
          else transs u T ts
      | (u as Free (_, T), ts) => transs u T ts
      | (Bound i, []) => pair (SVar i)
      | _ => raise TERM ("bad SMT term", [t]))
 
    and transs t T ts =
      let val (Us, U) = U.dest_funT (length ts) T
      in
        fold_map transT Us ##>> transT U #-> (fn Up =>
        add_fun t (SOME Up) ##>> fold_map trans ts #>> SApp)
      end

    val (us, trx') = fold_map trans ts trx
  in ((sign_of (header ts) dtyps trx', us), trx') end



(* translation *)

structure Configs = Generic_Data
(
  type T = (Proof.context -> config) U.dict
  val empty = []
  val extend = I
  fun merge xx = U.dict_merge fst xx
)

fun add_config (cs, cfg) = Configs.map (U.dict_update (cs, cfg))

fun translate ctxt comments ithms =
  let
    val cs = SMT_Config.solver_class_of ctxt
    val {prefixes, is_fol, header, has_datatypes, serialize} =
      (case U.dict_get (Configs.get (Context.Proof ctxt)) cs of
        SOME cfg => cfg ctxt
      | NONE => error ("SMT: no translation configuration found " ^
          "for solver class " ^ quote (U.string_of_class cs)))
      
    val with_datatypes =
      has_datatypes andalso Config.get ctxt SMT_Config.datatypes

    fun no_dtyps (tr_context, ctxt) ts = (([], tr_context, ctxt), ts)

    val (builtins, ts1) =
      ithms
      |> map (Envir.beta_eta_contract o U.prop_of o snd)
      |> mark_builtins ctxt

    val ((dtyps, tr_context, ctxt1), ts2) =
      ((make_tr_context prefixes, ctxt), ts1)
      |-> (if with_datatypes then collect_datatypes_and_records else no_dtyps)

    val (ctxt2, ts3) =
      ts2
      |> eta_expand
      |> lift_lambdas ctxt1
      ||> intro_explicit_application

    val ((rewrite_rules, extra_thms), ts4) =
      (if is_fol then folify ctxt2 builtins else pair ([], [])) ts3

    val rewrite_rules' = fun_app_eq :: rewrite_rules
  in
    (ts4, tr_context)
    |-> intermediate header dtyps ctxt2
    |>> uncurry (serialize comments)
    ||> recon_of ctxt2 rewrite_rules' extra_thms ithms revert_typ revert_types
  end

end
