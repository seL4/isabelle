(*  Title:      HOL/Tools/SMT/smt_translate.ML
    Author:     Sascha Boehme, TU Muenchen

Translate theorems into an SMT intermediate format and serialize them.
*)

signature SMT_TRANSLATE =
sig
  (* intermediate term structure *)
  datatype squant = SForall | SExists
  datatype 'a spattern = SPat of 'a list | SNoPat of 'a list
  datatype sterm =
    SVar of int |
    SApp of string * sterm list |
    SLet of string * sterm * sterm |
    SQua of squant * string list * sterm spattern list * sterm

  (* configuration options *)
  type prefixes = {sort_prefix: string, func_prefix: string}
  type header = Proof.context -> term list -> string list
  type strict = {
    is_builtin_conn: string * typ -> bool,
    is_builtin_pred: Proof.context -> string * typ -> bool,
    is_builtin_distinct: bool}
  type builtins = {
    builtin_typ: Proof.context -> typ -> string option,
    builtin_num: Proof.context -> typ -> int -> string option,
    builtin_fun: Proof.context -> string * typ -> term list ->
      (string * term list) option,
    has_datatypes: bool }
  type sign = {
    header: string list,
    sorts: string list,
    dtyps: (string * (string * (string * string) list) list) list list,
    funcs: (string * (string list * string)) list }
  type config = {
    prefixes: prefixes,
    header: header,
    strict: strict option,
    builtins: builtins,
    serialize: string list -> sign -> sterm list -> string }
  type recon = {
    typs: typ Symtab.table,
    terms: term Symtab.table,
    unfolds: thm list,
    assms: thm list }

  val translate: config -> Proof.context -> string list -> thm list ->
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
  SQua of squant * string list * sterm spattern list * sterm



(* configuration options *)

type prefixes = {sort_prefix: string, func_prefix: string}

type header = Proof.context -> term list -> string list

type strict = {
  is_builtin_conn: string * typ -> bool,
  is_builtin_pred: Proof.context -> string * typ -> bool,
  is_builtin_distinct: bool}

type builtins = {
  builtin_typ: Proof.context -> typ -> string option,
  builtin_num: Proof.context -> typ -> int -> string option,
  builtin_fun: Proof.context -> string * typ -> term list ->
    (string * term list) option,
  has_datatypes: bool }

type sign = {
  header: string list,
  sorts: string list,
  dtyps: (string * (string * (string * string) list) list) list list,
  funcs: (string * (string list * string)) list }

type config = {
  prefixes: prefixes,
  header: header,
  strict: strict option,
  builtins: builtins,
  serialize: string list -> sign -> sterm list -> string }

type recon = {
  typs: typ Symtab.table,
  terms: term Symtab.table,
  unfolds: thm list,
  assms: thm list }



(* utility functions *)

val dest_funT =
  let
    fun dest Ts 0 T = (rev Ts, T)
      | dest Ts i (Type ("fun", [T, U])) = dest (T::Ts) (i-1) U
      | dest _ _ T = raise TYPE ("dest_funT", [T], [])
  in dest [] end

val quantifier = (fn
    @{const_name All} => SOME SForall
  | @{const_name Ex} => SOME SExists
  | _ => NONE)

fun group_quant qname Ts (t as Const (q, _) $ Abs (_, T, u)) =
      if q = qname then group_quant qname (T :: Ts) u else (Ts, t)
  | group_quant _ Ts t = (Ts, t)

fun dest_pat (Const (@{const_name pat}, _) $ t) = (t, true)
  | dest_pat (Const (@{const_name nopat}, _) $ t) = (t, false)
  | dest_pat t = raise TERM ("dest_pat", [t])

fun dest_pats [] = I
  | dest_pats ts =
      (case map dest_pat ts |> split_list ||> distinct (op =) of
        (ps, [true]) => cons (SPat ps)
      | (ps, [false]) => cons (SNoPat ps)
      | _ => raise TERM ("dest_pats", ts))

fun dest_trigger (@{term trigger} $ tl $ t) =
      (rev (fold (dest_pats o HOLogic.dest_list) (HOLogic.dest_list tl) []), t)
  | dest_trigger t = ([], t)

fun dest_quant qn T t = quantifier qn |> Option.map (fn q =>
  let
    val (Ts, u) = group_quant qn [T] t
    val (ps, b) = dest_trigger u
  in (q, rev Ts, ps, b) end)

fun fold_map_pat f (SPat ts) = fold_map f ts #>> SPat
  | fold_map_pat f (SNoPat ts) = fold_map f ts #>> SNoPat

fun prop_of thm = HOLogic.dest_Trueprop (Thm.prop_of thm)



(* enforce a strict separation between formulas and terms *)

val term_eq_rewr = @{lemma "term_eq x y == x = y" by (simp add: term_eq_def)}

val term_bool = @{lemma "~(term_eq True False)" by (simp add: term_eq_def)}
val term_bool' = Simplifier.rewrite_rule [term_eq_rewr] term_bool


val needs_rewrite = Thm.prop_of #> Term.exists_subterm (fn
    Const (@{const_name Let}, _) => true
  | @{term "op = :: bool => _"} $ _ $ @{term True} => true
  | Const (@{const_name If}, _) $ _ $ @{term True} $ @{term False} => true
  | _ => false)

val rewrite_rules = [
  Let_def,
  @{lemma "P = True == P" by (rule eq_reflection) simp},
  @{lemma "if P then True else False == P" by (rule eq_reflection) simp}]

fun rewrite ctxt = Simplifier.full_rewrite
  (Simplifier.context ctxt empty_ss addsimps rewrite_rules)

fun normalize ctxt thm =
  if needs_rewrite thm then Conv.fconv_rule (rewrite ctxt) thm else thm

val unfold_rules = term_eq_rewr :: rewrite_rules


val revert_types =
  let
    fun revert @{typ prop} = @{typ bool}
      | revert (Type (n, Ts)) = Type (n, map revert Ts)
      | revert T = T
  in Term.map_types revert end


fun strictify {is_builtin_conn, is_builtin_pred, is_builtin_distinct} ctxt =
  let
    fun is_builtin_conn' (@{const_name True}, _) = false
      | is_builtin_conn' (@{const_name False}, _) = false
      | is_builtin_conn' c = is_builtin_conn c

    val propT = @{typ prop} and boolT = @{typ bool}
    val as_propT = (fn @{typ bool} => propT | T => T)
    fun mapTs f g = Term.strip_type #> (fn (Ts, T) => map f Ts ---> g T)
    fun conn (n, T) = (n, mapTs as_propT as_propT T)
    fun pred (n, T) = (n, mapTs I as_propT T)

    val term_eq = @{term "op = :: bool => _"} |> Term.dest_Const |> pred
    fun as_term t = Const term_eq $ t $ @{term True}

    val if_term = Const (@{const_name If}, [propT, boolT, boolT] ---> boolT)
    fun wrap_in_if t = if_term $ t $ @{term True} $ @{term False}

    fun in_list T f t = HOLogic.mk_list T (map f (HOLogic.dest_list t))

    fun in_term t =
      (case Term.strip_comb t of
        (c as Const (@{const_name If}, _), [t1, t2, t3]) =>
          c $ in_form t1 $ in_term t2 $ in_term t3
      | (h as Const c, ts) =>
          if is_builtin_conn' (conn c) orelse is_builtin_pred ctxt (pred c)
          then wrap_in_if (in_form t)
          else Term.list_comb (h, map in_term ts)
      | (h as Free _, ts) => Term.list_comb (h, map in_term ts)
      | _ => t)

    and in_pat ((c as Const (@{const_name pat}, _)) $ t) = c $ in_term t
      | in_pat ((c as Const (@{const_name nopat}, _)) $ t) = c $ in_term t
      | in_pat t = raise TERM ("in_pat", [t])

    and in_pats ps =
      in_list @{typ "pattern list"} (in_list @{typ pattern} in_pat) ps

    and in_trig ((c as @{term trigger}) $ p $ t) = c $ in_pats p $ in_form t
      | in_trig t = in_form t

    and in_form t =
      (case Term.strip_comb t of
        (q as Const (qn, _), [Abs (n, T, t')]) =>
          if is_some (quantifier qn) then q $ Abs (n, T, in_trig t')
          else as_term (in_term t)
      | (Const (c as (@{const_name distinct}, T)), [t']) =>
          if is_builtin_distinct then Const (pred c) $ in_list T in_term t'
          else as_term (in_term t)
      | (Const c, ts) =>
          if is_builtin_conn (conn c)
          then Term.list_comb (Const (conn c), map in_form ts)
          else if is_builtin_pred ctxt (pred c)
          then Term.list_comb (Const (pred c), map in_term ts)
          else as_term (in_term t)
      | _ => as_term (in_term t))
  in
    map (normalize ctxt) #> (fn thms => ((unfold_rules, term_bool' :: thms),
    map (in_form o prop_of) (term_bool :: thms)))
  end



(* translation from Isabelle terms into SMT intermediate terms *)

val empty_context = (1, Typtab.empty, [], 1, Termtab.empty)

fun make_sign header (_, typs, dtyps, _, terms) = {
  header = header,
  sorts = Typtab.fold (fn (_, (n, true)) => cons n | _ => I) typs [],
  funcs = Termtab.fold (fn (_, (n, SOME ss)) => cons (n,ss) | _ => I) terms [],
  dtyps = rev dtyps }

fun make_recon (unfolds, assms) (_, typs, _, _, terms) = {
  typs = Symtab.make (map (apfst fst o swap) (Typtab.dest typs)),
    (*FIXME: don't drop the datatype information! *)
  terms = Symtab.make (map (fn (t, (n, _)) => (n, t)) (Termtab.dest terms)),
  unfolds = unfolds,
  assms = assms }

fun string_of_index pre i = pre ^ string_of_int i

fun new_typ sort_prefix proper T (Tidx, typs, dtyps, idx, terms) =
  let val s = string_of_index sort_prefix Tidx
  in (s, (Tidx+1, Typtab.update (T, (s, proper)) typs, dtyps, idx, terms)) end

fun lookup_typ (_, typs, _, _, _) = Typtab.lookup typs

fun fresh_typ T f cx =
  (case lookup_typ cx T of
    SOME (s, _) => (s, cx)
  | NONE => f T cx)

fun new_fun func_prefix t ss (Tidx, typs, dtyps, idx, terms) =
  let
    val f = string_of_index func_prefix idx
    val terms' = Termtab.update (revert_types t, (f, ss)) terms
  in (f, (Tidx, typs, dtyps, idx+1, terms')) end

fun fresh_fun func_prefix t ss (cx as (_, _, _, _, terms)) =
  (case Termtab.lookup terms t of
    SOME (f, _) => (f, cx)
  | NONE => new_fun func_prefix t ss cx)

fun mk_type (_, Tfs) (d as Datatype.DtTFree _) = the (AList.lookup (op =) Tfs d)
  | mk_type Ts (Datatype.DtType (n, ds)) = Type (n, map (mk_type Ts) ds)
  | mk_type (Tds, _) (Datatype.DtRec i) = nth Tds i

fun mk_selector ctxt Ts T n (i, d) =
  (case Datatype_Selectors.lookup_selector ctxt (n, i+1) of
    NONE => raise Fail ("missing selector for datatype constructor " ^ quote n)
  | SOME m => mk_type Ts d |> (fn U => (Const (m, T --> U), U)))

fun mk_constructor ctxt Ts T (n, args) =
  let val (sels, Us) = split_list (map_index (mk_selector ctxt Ts T n) args)
  in (Const (n, Us ---> T), sels) end

fun lookup_datatype ctxt n Ts = if n = @{type_name bool} then NONE else
  (case Datatype.get_info (ProofContext.theory_of ctxt) n of
    NONE => NONE  (* FIXME: also use Record.get_info *)
  | SOME {descr, ...} =>
      let
        val Tds = map (fn (_, (tn, _, _)) => Type (tn, Ts))
          (sort (int_ord o pairself fst) descr)
        val Tfs = (case hd descr of (_, (_, tfs, _)) => tfs ~~ Ts)
      in
        SOME (descr |> map (fn (i, (_, _, cs)) =>
          (nth Tds i, map (mk_constructor ctxt (Tds, Tfs) (nth Tds i)) cs)))
      end)

fun relaxed thms = (([], thms), map prop_of thms)

fun with_context header f (ths, ts) =
  let val (us, context) = fold_map f ts empty_context
  in ((make_sign (header ts) context, us), make_recon ths context) end


fun translate {prefixes, strict, header, builtins, serialize} ctxt comments =
  let
    val {sort_prefix, func_prefix} = prefixes
    val {builtin_typ, builtin_num, builtin_fun, has_datatypes} = builtins

    fun transT (T as TFree _) = fresh_typ T (new_typ sort_prefix true)
      | transT (T as TVar _) = (fn _ => raise TYPE ("smt_translate", [T], []))
      | transT (T as Type (n, Ts)) =
          (case builtin_typ ctxt T of
            SOME n => pair n
          | NONE => fresh_typ T (fn _ => fn cx =>
              if not has_datatypes then new_typ sort_prefix true T cx
              else
                (case lookup_datatype ctxt n Ts of
                  NONE => new_typ sort_prefix true T cx
                | SOME dts =>
                    let val cx' = new_dtyps dts cx 
                    in (fst (the (lookup_typ cx' T)), cx') end)))

    and new_dtyps dts cx =
      let
        fun new_decl i t =
          let val (Ts, T) = dest_funT i (Term.fastype_of t)
          in
            fold_map transT Ts ##>> transT T ##>>
            new_fun func_prefix t NONE #>> swap
          end
        fun new_dtyp_decl (con, sels) =
          new_decl (length sels) con ##>> fold_map (new_decl 1) sels #>>
          (fn ((con', _), sels') => (con', map (apsnd snd) sels'))
      in
        cx
        |> fold_map (new_typ sort_prefix false o fst) dts
        ||>> fold_map (fold_map new_dtyp_decl o snd) dts
        |-> (fn (ss, decls) => fn (Tidx, typs, dtyps, idx, terms) =>
              (Tidx, typs, (ss ~~ decls) :: dtyps, idx, terms))
      end

    fun app n ts = SApp (n, ts)

    fun trans t =
      (case Term.strip_comb t of
        (Const (qn, _), [Abs (_, T, t1)]) =>
          (case dest_quant qn T t1 of
            SOME (q, Ts, ps, b) =>
              fold_map transT Ts ##>> fold_map (fold_map_pat trans) ps ##>>
              trans b #>> (fn ((Ts', ps'), b') => SQua (q, Ts', ps', b'))
          | NONE => raise TERM ("intermediate", [t]))
      | (Const (@{const_name Let}, _), [t1, Abs (_, T, t2)]) =>
          transT T ##>> trans t1 ##>> trans t2 #>>
          (fn ((U, u1), u2) => SLet (U, u1, u2))
      | (h as Const (c as (@{const_name distinct}, T)), [t1]) =>
          (case builtin_fun ctxt c (HOLogic.dest_list t1) of
            SOME (n, ts) => fold_map trans ts #>> app n
          | NONE => transs h T [t1])
      | (h as Const (c as (_, T)), ts) =>
          (case try HOLogic.dest_number t of
            SOME (T, i) =>
              (case builtin_num ctxt T i of
                SOME n => pair (SApp (n, []))
              | NONE => transs t T [])
          | NONE =>
              (case builtin_fun ctxt c ts of
                SOME (n, ts') => fold_map trans ts' #>> app n
              | NONE => transs h T ts))
      | (h as Free (_, T), ts) => transs h T ts
      | (Bound i, []) => pair (SVar i)
      | _ => raise TERM ("smt_translate", [t]))

    and transs t T ts =
      let val (Us, U) = dest_funT (length ts) T
      in
        fold_map transT Us ##>> transT U #-> (fn Up =>
        fresh_fun func_prefix t (SOME Up) ##>> fold_map trans ts #>> SApp)
      end
  in
    (case strict of SOME strct => strictify strct ctxt | NONE => relaxed) #>
    with_context (header ctxt) trans #>> uncurry (serialize comments)
  end

end
