(*  Title:      HOL/SMT/Tools/smt_translate.ML
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
  type strict = {
    is_builtin_conn: string * typ -> bool,
    is_builtin_pred: string * typ -> bool,
    is_builtin_distinct: bool}
  type builtins = {
    builtin_typ: typ -> string option,
    builtin_num: typ -> int -> string option,
    builtin_fun: string * typ -> term list -> (string * term list) option }
  datatype smt_theory = Integer | Real | Bitvector
  type sign = {
    theories: smt_theory list,
    sorts: string list,
    funcs: (string * (string list * string)) list }
  type config = {
    prefixes: prefixes,
    strict: strict option,
    builtins: builtins,
    serialize: sign -> sterm list -> string }
  type recon = {
    typs: typ Symtab.table,
    terms: term Symtab.table,
    unfolds: thm list,
    assms: thm list option }

  val translate: config -> Proof.context -> thm list -> string * recon
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

type strict = {
  is_builtin_conn: string * typ -> bool,
  is_builtin_pred: string * typ -> bool,
  is_builtin_distinct: bool}

type builtins = {
  builtin_typ: typ -> string option,
  builtin_num: typ -> int -> string option,
  builtin_fun: string * typ -> term list -> (string * term list) option }

datatype smt_theory = Integer | Real | Bitvector

type sign = {
  theories: smt_theory list,
  sorts: string list,
  funcs: (string * (string list * string)) list }

type config = {
  prefixes: prefixes,
  strict: strict option,
  builtins: builtins,
  serialize: sign -> sterm list -> string }

type recon = {
  typs: typ Symtab.table,
  terms: term Symtab.table,
  unfolds: thm list,
  assms: thm list option }



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

fun dest_pat ts (Const (@{const_name pat}, _) $ t) = SPat (rev (t :: ts))
  | dest_pat ts (Const (@{const_name nopat}, _) $ t) = SNoPat (rev (t :: ts))
  | dest_pat ts (Const (@{const_name andpat}, _) $ p $ t) = dest_pat (t::ts) p
  | dest_pat _ t = raise TERM ("dest_pat", [t])

fun dest_trigger (@{term trigger} $ tl $ t) =
      (map (dest_pat []) (HOLogic.dest_list tl), t)
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

val term_eq_rewr = @{lemma "x term_eq y == x = y" by (simp add: term_eq_def)}

val term_bool = @{lemma "~(True term_eq False)" by (simp add: term_eq_def)}
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
          if is_builtin_conn' (conn c) orelse is_builtin_pred (pred c)
          then wrap_in_if (in_form t)
          else Term.list_comb (h, map in_term ts)
      | (h as Free _, ts) => Term.list_comb (h, map in_term ts)
      | _ => t)

    and in_pat ((c as Const (@{const_name pat}, _)) $ t) = c $ in_term t
      | in_pat ((c as Const (@{const_name nopat}, _)) $ t) = c $ in_term t
      | in_pat ((c as Const (@{const_name andpat}, _)) $ p $ t) =
          c $ in_pat p $ in_term t
      | in_pat t = raise TERM ("in_pat", [t])

    and in_pats p = in_list @{typ pattern} in_pat p

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
          else if is_builtin_pred (pred c)
          then Term.list_comb (Const (pred c), map in_term ts)
          else as_term (in_term t)
      | _ => as_term (in_term t))
  in
    map (normalize ctxt) #> (fn thms => ((unfold_rules, term_bool' :: thms),
    map (in_form o prop_of) (term_bool :: thms)))
  end



(* translation from Isabelle terms into SMT intermediate terms *)

val empty_context = (1, Typtab.empty, 1, Termtab.empty, [])

fun make_sign (_, typs, _, terms, thys) = {
  theories = thys,
  sorts = Typtab.fold (cons o snd) typs [],
  funcs = Termtab.fold (cons o snd) terms [] }

fun make_recon (unfolds, assms) (_, typs, _, terms, _) = {
  typs = Symtab.make (map swap (Typtab.dest typs)),
  terms = Symtab.make (map (fn (t, (n, _)) => (n, t)) (Termtab.dest terms)),
  unfolds = unfolds,
  assms = SOME assms }

fun string_of_index pre i = pre ^ string_of_int i

fun add_theory T (Tidx, typs, idx, terms, thys) =
  let
    fun add @{typ int} = insert (op =) Integer
      | add @{typ real} = insert (op =) Real
      | add (Type (@{type_name word}, _)) = insert (op =) Bitvector
      | add (Type (_, Ts)) = fold add Ts
      | add _ = I
  in (Tidx, typs, idx, terms, add T thys) end

fun fresh_typ sort_prefix T (cx as (Tidx, typs, idx, terms, thys)) =
  (case Typtab.lookup typs T of
    SOME s => (s, cx)
  | NONE =>
      let
        val s = string_of_index sort_prefix Tidx
        val typs' = Typtab.update (T, s) typs
      in (s, (Tidx+1, typs', idx, terms, thys)) end)

fun fresh_fun func_prefix t ss (cx as (Tidx, typs, idx, terms, thys)) =
  (case Termtab.lookup terms t of
    SOME (f, _) => (f, cx)
  | NONE =>
      let
        val f = string_of_index func_prefix idx
        val terms' = Termtab.update (revert_types t, (f, ss)) terms
      in (f, (Tidx, typs, idx+1, terms', thys)) end)

fun relaxed thms = (([], thms), map prop_of thms)

fun with_context f (ths, ts) =
  let val (us, context) = fold_map f ts empty_context
  in ((make_sign context, us), make_recon ths context) end


fun translate {prefixes, strict, builtins, serialize} ctxt =
  let
    val {sort_prefix, func_prefix} = prefixes
    val {builtin_typ, builtin_num, builtin_fun} = builtins

    fun transT T = add_theory T #>
      (case builtin_typ T of
        SOME n => pair n
      | NONE => fresh_typ sort_prefix T)

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
          (case builtin_fun c (HOLogic.dest_list t1) of
            SOME (n, ts) => add_theory T #> fold_map trans ts #>> app n
          | NONE => transs h T [t1])
      | (h as Const (c as (_, T)), ts) =>
          (case try HOLogic.dest_number t of
            SOME (T, i) =>
              (case builtin_num T i of
                SOME n => add_theory T #> pair (SApp (n, []))
              | NONE => transs t T [])
          | NONE =>
              (case builtin_fun c ts of
                SOME (n, ts') => add_theory T #> fold_map trans ts' #>> app n
              | NONE => transs h T ts))
      | (h as Free (_, T), ts) => transs h T ts
      | (Bound i, []) => pair (SVar i)
      | _ => raise TERM ("intermediate", [t]))

    and transs t T ts =
      let val (Us, U) = dest_funT (length ts) T
      in
        fold_map transT Us ##>> transT U #-> (fn Up =>
        fresh_fun func_prefix t Up ##>> fold_map trans ts #>> SApp)
      end
  in
    (if is_some strict then strictify (the strict) ctxt else relaxed) #>
    with_context trans #>> uncurry serialize
  end

end
