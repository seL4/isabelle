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

  (*configuration options*)
  type prefixes = {sort_prefix: string, func_prefix: string}
  type sign = {
    header: string list,
    sorts: string list,
    dtyps: (string * (string * (string * string) list) list) list list,
    funcs: (string * (string list * string)) list }
  type config = {
    prefixes: prefixes,
    header: Proof.context -> term list -> string list,
    is_fol: bool,
    has_datatypes: bool,
    serialize: string list -> sign -> sterm list -> string }
  type recon = {
    typs: typ Symtab.table,
    terms: term Symtab.table,
    unfolds: thm list,
    assms: (int * thm) list }

  val translate: config -> Proof.context -> string list -> (int * thm) list ->
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



(* configuration options *)

type prefixes = {sort_prefix: string, func_prefix: string}

type sign = {
  header: string list,
  sorts: string list,
  dtyps: (string * (string * (string * string) list) list) list list,
  funcs: (string * (string list * string)) list }

type config = {
  prefixes: prefixes,
  header: Proof.context -> term list -> string list,
  is_fol: bool,
  has_datatypes: bool,
  serialize: string list -> sign -> sterm list -> string }

type recon = {
  typs: typ Symtab.table,
  terms: term Symtab.table,
  unfolds: thm list,
  assms: (int * thm) list }



(* utility functions *)

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
  | dest_pat t = raise TERM ("dest_pat", [t])

fun dest_pats [] = I
  | dest_pats ts =
      (case map dest_pat ts |> split_list ||> distinct (op =) of
        (ps, [true]) => cons (SPat ps)
      | (ps, [false]) => cons (SNoPat ps)
      | _ => raise TERM ("dest_pats", ts))

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

fun prop_of thm = HOLogic.dest_Trueprop (Thm.prop_of thm)



(* map HOL formulas to FOL formulas (i.e., separate formulas froms terms) *)

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
  in Term.map_aterms replace (prop_of term_bool) end

val needs_rewrite = Thm.prop_of #> Term.exists_subterm (fn
    Const (@{const_name Let}, _) => true
  | @{const HOL.eq (bool)} $ _ $ @{const True} => true
  | Const (@{const_name If}, _) $ _ $ @{const True} $ @{const False} => true
  | _ => false)

val rewrite_rules = [
  Let_def,
  @{lemma "P = True == P" by (rule eq_reflection) simp},
  @{lemma "if P then True else False == P" by (rule eq_reflection) simp}]

fun rewrite ctxt ct =
  Conv.top_sweep_conv (fn ctxt' =>
    Conv.rewrs_conv rewrite_rules then_conv rewrite ctxt') ctxt ct

fun normalize ctxt thm =
  if needs_rewrite thm then Conv.fconv_rule (rewrite ctxt) thm else thm

fun revert_typ @{typ SMT.term_bool} = @{typ bool}
  | revert_typ (Type (n, Ts)) = Type (n, map revert_typ Ts)
  | revert_typ T = T

val revert_types = Term.map_types revert_typ

fun folify ctxt =
  let
    fun is_builtin_conn (@{const_name True}, _) _ = false
      | is_builtin_conn (@{const_name False}, _) _ = false
      | is_builtin_conn c ts = B.is_builtin_conn ctxt c ts

    fun as_term t = @{const HOL.eq (SMT.term_bool)} $ t $ term_true

    fun as_tbool @{typ bool} = tboolT
      | as_tbool (Type (n, Ts)) = Type (n, map as_tbool Ts)
      | as_tbool T = T
    fun mapTs f g = Term.strip_type #> (fn (Ts, T) => map f Ts ---> g T)
    fun predT T = mapTs as_tbool I T
    fun funcT T = mapTs as_tbool as_tbool T
    fun func (n, T) = Const (n, funcT T)

    fun map_ifT T = T |> Term.dest_funT ||> funcT |> (op -->)
    val if_term = @{const If (bool)} |> Term.dest_Const ||> map_ifT |> Const
    fun wrap_in_if t = if_term $ t $ term_true $ term_false

    fun in_list T f t = HOLogic.mk_list T (map f (HOLogic.dest_list t))

    fun in_term t =
      (case Term.strip_comb t of
        (Const (c as @{const_name If}, T), [t1, t2, t3]) =>
          Const (c, map_ifT T) $ in_form t1 $ in_term t2 $ in_term t3
      | (Const c, ts) =>
          if is_builtin_conn c ts orelse B.is_builtin_pred ctxt c ts
          then wrap_in_if (in_form t)
          else Term.list_comb (func c, map in_term ts)
      | (Free (n, T), ts) => Term.list_comb (Free (n, funcT T), map in_term ts)
      | _ => t)

    and in_weight ((c as @{const SMT.weight}) $ w $ t) = c $ w $ in_form t
      | in_weight t = in_form t 

    and in_pat (Const (c as (@{const_name pat}, _)) $ t) = func c $ in_term t
      | in_pat (Const (c as (@{const_name nopat}, _)) $ t) = func c $ in_term t
      | in_pat t = raise TERM ("in_pat", [t])

    and in_pats ps =
      in_list @{typ "pattern list"} (in_list @{typ pattern} in_pat) ps

    and in_trig ((c as @{const trigger}) $ p $ t) = c $ in_pats p $ in_weight t
      | in_trig t = in_weight t

    and in_form t =
      (case Term.strip_comb t of
        (q as Const (qn, _), [Abs (n, T, t')]) =>
          if is_some (quantifier qn) then q $ Abs (n, as_tbool T, in_trig t')
          else as_term (in_term t)
      | (Const (c as (n as @{const_name distinct}, T)), [t']) =>
          if B.is_builtin_fun ctxt c [t'] then
            Const (n, predT T) $ in_list T in_term t'
          else as_term (in_term t)
      | (Const (c as (n, T)), ts) =>
          if B.is_builtin_conn ctxt c ts
          then Term.list_comb (Const c, map in_form ts)
          else if B.is_builtin_pred ctxt c ts
          then Term.list_comb (Const (n, predT T), map in_term ts)
          else as_term (in_term t)
      | _ => as_term (in_term t))
  in
    map (apsnd (normalize ctxt)) #> (fn irules =>
    ((rewrite_rules, (~1, term_bool) :: irules),
     term_bool_prop :: map (in_form o prop_of o snd) irules))
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
  let
    val s = string_of_index sort_prefix Tidx
    val U = revert_typ T
  in (s, (Tidx+1, Typtab.update (U, (s, proper)) typs, dtyps, idx, terms)) end

fun lookup_typ (_, typs, _, _, _) = Typtab.lookup typs o revert_typ

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
  (case Termtab.lookup terms (revert_types t) of
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

fun lookup_datatype ctxt n Ts =
  if member (op =) [@{type_name bool}, @{type_name nat}] n then NONE
  else
    Datatype.get_info (ProofContext.theory_of ctxt) n
    |> Option.map (fn {descr, ...} =>
         let
           val Tds = map (fn (_, (tn, _, _)) => Type (tn, Ts))
             (sort (int_ord o pairself fst) descr)
           val Tfs = (case hd descr of (_, (_, tfs, _)) => tfs ~~ Ts)
         in
           descr |> map (fn (i, (_, _, cs)) =>
             (nth Tds i, map (mk_constructor ctxt (Tds, Tfs) (nth Tds i)) cs))
         end)

fun relaxed irules = (([], irules), map (prop_of o snd) irules)

fun with_context header f (ths, ts) =
  let val (us, context) = fold_map f ts empty_context
  in ((make_sign (header ts) context, us), make_recon ths context) end


fun translate config ctxt comments =
  let
    val {prefixes, is_fol, header, has_datatypes, serialize} = config
    val {sort_prefix, func_prefix} = prefixes

    fun transT (T as TFree _) = fresh_typ T (new_typ sort_prefix true)
      | transT (T as TVar _) = (fn _ => raise TYPE ("smt_translate", [T], []))
      | transT (T as Type (n, Ts)) =
          (case B.builtin_typ ctxt T of
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
          let val (Ts, T) = U.dest_funT i (Term.fastype_of t)
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
            SOME (q, Ts, ps, w, b) =>
              fold_map transT Ts ##>> fold_map (fold_map_pat trans) ps ##>>
              trans b #>> (fn ((Ts', ps'), b') => SQua (q, Ts', ps', w, b'))
          | NONE => raise TERM ("intermediate", [t]))
      | (Const (@{const_name Let}, _), [t1, Abs (_, T, t2)]) =>
          transT T ##>> trans t1 ##>> trans t2 #>>
          (fn ((U, u1), u2) => SLet (U, u1, u2))
      | (h as Const (c as (@{const_name distinct}, T)), ts) =>
          (case B.builtin_fun ctxt c ts of
            SOME (n, ts) => fold_map trans ts #>> app n
          | NONE => transs h T ts)
      | (h as Const (c as (_, T)), ts) =>
          (case B.builtin_num ctxt t of
            SOME n => pair (SApp (n, []))
          | NONE =>
              (case B.builtin_fun ctxt c ts of
                SOME (n, ts') => fold_map trans ts' #>> app n
              | NONE => transs h T ts))
      | (h as Free (_, T), ts) => transs h T ts
      | (Bound i, []) => pair (SVar i)
      | (Abs (_, _, t1 $ Bound 0), []) =>
        if not (loose_bvar1 (t1, 0)) then trans t1 (* eta-reduce on the fly *)
        else raise TERM ("smt_translate", [t])
      | _ => raise TERM ("smt_translate", [t]))

    and transs t T ts =
      let val (Us, U) = U.dest_funT (length ts) T
      in
        fold_map transT Us ##>> transT U #-> (fn Up =>
        fresh_fun func_prefix t (SOME Up) ##>> fold_map trans ts #>> SApp)
      end
  in
    (if is_fol then folify ctxt else relaxed) #>
    with_context (header ctxt) trans #>> uncurry (serialize comments)
  end

end
