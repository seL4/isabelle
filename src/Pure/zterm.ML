(*  Title:      Pure/zterm.ML
    Author:     Makarius

Tight representation of types / terms / proof terms, notably for proof recording.
*)

(* global datatypes *)

datatype ztyp =
    ZTVar of indexname * sort      (*free: index ~1*)
  | ZFun of ztyp * ztyp
  | ZProp
  | ZItself of ztyp
  | ZType0 of string               (*type constant*)
  | ZType1 of string * ztyp        (*type constructor: 1 argument*)
  | ZType of string * ztyp list    (*type constructor: >= 2 arguments*)

datatype zterm =
    ZVar of indexname * ztyp       (*free: index ~1*)
  | ZBound of int
  | ZConst0 of string              (*monomorphic constant*)
  | ZConst1 of string * ztyp       (*polymorphic constant: 1 type argument*)
  | ZConst of string * ztyp list   (*polymorphic constant: >= 2 type arguments*)
  | ZAbs of string * ztyp * zterm
  | ZApp of zterm * zterm
  | ZClass of ztyp * class         (*OFCLASS proposition*)

datatype zproof =
    ZDummy                         (*dummy proof*)
  | ZBoundP of int
  | ZHyp of zterm
  | ZAbst of string * ztyp * zproof
  | ZAbsP of string * zterm * zproof
  | ZAppt of zproof * zterm
  | ZAppP of zproof * zproof
  | ZClassP of ztyp * class        (*OFCLASS proof from sorts algebra*)
  | ZAxiom of {name: string, oracle: bool} * zterm * ztyp list;

signature ZTVARS =
sig
  include TERM_ITEMS
  val add_tvarsT: ztyp -> set -> set
  val add_tvars: zterm -> set -> set
end

signature ZTERM =
sig
  datatype ztyp = datatype ztyp
  datatype zterm = datatype zterm
  datatype zproof = datatype zproof
  val fold_tvars: (indexname * sort -> 'a -> 'a) -> ztyp -> 'a -> 'a
  val fold_aterms: (zterm -> 'a -> 'a) -> zterm -> 'a -> 'a
  val fold_types: (ztyp -> 'a -> 'a) -> zterm -> 'a -> 'a
  structure ZTVars: ZTVARS
  val ztyp_ord: ztyp * ztyp -> order
  val aconv_zterm: zterm * zterm -> bool
  val ztyp_of: typ -> ztyp
  val typ_of: ztyp -> typ
  val zterm_of: Consts.T -> term -> zterm
  val term_of: Consts.T -> zterm -> term
  val global_zterm_of: theory -> term -> zterm
  val global_term_of: theory -> zterm -> term
  val dummy_proof: 'a -> zproof
  val todo_proof: 'a -> zproof
  val axiom_proof:  theory -> {name: string, oracle: bool} -> term -> zproof
  val assume_proof: theory -> term -> zproof
  val trivial_proof: theory -> term -> zproof
  val implies_intr_proof: theory -> term -> zproof -> zproof
  val forall_intr_proof: theory -> string * term -> typ -> zproof -> zproof
  val forall_elim_proof: theory -> term -> zproof -> zproof
end;

structure ZTerm: ZTERM =
struct

datatype ztyp = datatype ztyp;
datatype zterm = datatype zterm;
datatype zproof = datatype zproof;


(* fold *)

fun fold_tvars f (ZTVar v) = f v
  | fold_tvars f (ZFun (T, U)) = fold_tvars f T #> fold_tvars f U
  | fold_tvars f (ZItself T) = fold_tvars f T
  | fold_tvars f (ZType1 (_, T)) = fold_tvars f T
  | fold_tvars f (ZType (_, Ts)) = fold (fold_tvars f) Ts
  | fold_tvars _ _ = I;

fun fold_aterms f (ZApp (t, u)) = fold_aterms f t #> fold_aterms f u
  | fold_aterms f (ZAbs (_, _, t)) = fold_aterms f t
  | fold_aterms f a = f a;

fun fold_types f (ZVar (_, T)) = f T
  | fold_types f (ZConst1 (_, T)) = f T
  | fold_types f (ZConst (_, As)) = fold f As
  | fold_types f (ZAbs (_, T, b)) = f T #> fold_types f b
  | fold_types f (ZApp (t, u)) = fold_types f t #> fold_types f u
  | fold_types f (ZClass (T, _)) = f T
  | fold_types _ _ = I;


(* term items *)

structure ZTVars: ZTVARS =
struct
  open TVars;
  val add_tvarsT = fold_tvars add_set;
  val add_tvars = fold_types add_tvarsT;
end;

val make_tvars = ZTVars.list_set o ZTVars.build o ZTVars.add_tvars;


(* orderings *)

local

fun cons_nr (ZTVar _) = 0
  | cons_nr (ZFun _) = 1
  | cons_nr ZProp = 2
  | cons_nr (ZItself _) = 3
  | cons_nr (ZType0 _) = 4
  | cons_nr (ZType1 _) = 5
  | cons_nr (ZType _) = 6;

val fast_indexname_ord = Term_Ord.fast_indexname_ord;
val sort_ord = Term_Ord.sort_ord;

in

fun ztyp_ord TU =
  if pointer_eq TU then EQUAL
  else
    (case TU of
      (ZTVar (a, A), ZTVar (b, B)) =>
        (case fast_indexname_ord (a, b) of EQUAL => sort_ord (A, B) | ord => ord)
    | (ZFun (T, T'), ZFun (U, U')) =>
        (case ztyp_ord (T, U) of EQUAL => ztyp_ord (T', U') | ord => ord)
    | (ZProp, ZProp) => EQUAL
    | (ZItself T, ZItself U) => ztyp_ord (T, U)
    | (ZType0 a, ZType0 b) => fast_string_ord (a, b)
    | (ZType1 (a, T), ZType1 (b, U)) =>
        (case fast_string_ord (a, b) of EQUAL => ztyp_ord (T, U) | ord => ord)
    | (ZType (a, Ts), ZType (b, Us)) =>
        (case fast_string_ord (a, b) of EQUAL => dict_ord ztyp_ord (Ts, Us) | ord => ord)
    | (T, U) => int_ord (cons_nr T, cons_nr U));

end;


(* alpha conversion *)

fun aconv_zterm (tm1, tm2) =
  pointer_eq (tm1, tm2) orelse
    (case (tm1, tm2) of
      (ZApp (t1, u1), ZApp (t2, u2)) => aconv_zterm (t1, t2) andalso aconv_zterm (u1, u2)
    | (ZAbs (_, T1, t1), ZAbs (_, T2, t2)) => aconv_zterm (t1, t2) andalso T1 = T2
    | (a1, a2) => a1 = a2);


(* convert ztyp / zterm vs. regular typ / term *)

fun ztyp_of (TFree (a, S)) = ZTVar ((a, ~1), S)
  | ztyp_of (TVar v) = ZTVar v
  | ztyp_of (Type ("fun", [T, U])) = ZFun (ztyp_of T, ztyp_of U)
  | ztyp_of (Type (c, [])) = if c = "prop" then ZProp else ZType0 c
  | ztyp_of (Type (c, [T])) = if c = "itself" then ZItself (ztyp_of T) else ZType1 (c, ztyp_of T)
  | ztyp_of (Type (c, ts)) = ZType (c, map ztyp_of ts);

fun typ_of (ZTVar ((a, ~1), S)) = TFree (a, S)
  | typ_of (ZTVar v) = TVar v
  | typ_of (ZFun (T, U)) = typ_of T --> typ_of U
  | typ_of ZProp = propT
  | typ_of (ZItself T) = Term.itselfT (typ_of T)
  | typ_of (ZType0 c) = Type (c, [])
  | typ_of (ZType1 (c, T)) = Type (c, [typ_of T])
  | typ_of (ZType (c, Ts)) = Type (c, map typ_of Ts);

fun zterm_of consts =
  let
    val typargs = Consts.typargs consts;
    fun zterm (Free (x, T)) = ZVar ((x, ~1), ztyp_of T)
      | zterm (Var (xi, T)) = ZVar (xi, ztyp_of T)
      | zterm (Bound i) = ZBound i
      | zterm (Const (c, T)) =
          (case typargs (c, T) of
            [] => ZConst0 c
          | [T] => ZConst1 (c, ztyp_of T)
          | Ts => ZConst (c, map ztyp_of Ts))
      | zterm (Abs (a, T, b)) = ZAbs (a, ztyp_of T, zterm b)
      | zterm ((t as Const (c, _)) $ (u as Const ("Pure.type", _))) =
          if String.isSuffix Logic.class_suffix c then
            ZClass (ztyp_of (Logic.dest_type u), Logic.class_of_const c)
          else ZApp (zterm t, zterm u)
      | zterm (t $ u) = ZApp (zterm t, zterm u);
  in zterm end;

fun term_of consts =
  let
    val instance = Consts.instance consts;
    fun const (c, Ts) = Const (c, instance (c, Ts));
    fun term (ZVar ((x, ~1), T)) = Free (x, typ_of T)
      | term (ZVar (xi, T)) = Var (xi, typ_of T)
      | term (ZBound i) = Bound i
      | term (ZConst0 c) = const (c, [])
      | term (ZConst1 (c, T)) = const (c, [typ_of T])
      | term (ZConst (c, Ts)) = const (c, map typ_of Ts)
      | term (ZAbs (a, T, b)) = Abs (a, typ_of T, term b)
      | term (ZApp (t, u)) = term t $ term u
      | term (ZClass (T, c)) = Logic.mk_of_class (typ_of T, c);
  in term end;

val global_zterm_of = zterm_of o Sign.consts_of;
val global_term_of = term_of o Sign.consts_of;



(** proof construction **)

fun dummy_proof _ = ZDummy;
val todo_proof = dummy_proof;

fun axiom_proof thy a A =
  let
    val t = global_zterm_of thy A;
    val Ts = make_tvars t;
  in ZAxiom (a, t, map ZTVar Ts) end;

fun assume_proof thy A =
  ZHyp (global_zterm_of thy A);

fun trivial_proof thy A =
  ZAbsP ("H", global_zterm_of thy A, ZBoundP 0);

fun implies_intr_proof thy A prf =
  let
    val h = global_zterm_of thy A;
    fun abs_hyp i (p as ZHyp t) = if aconv_zterm (h, t) then ZBoundP i else p
      | abs_hyp i (ZAbst (x, T, p)) = ZAbst (x, T, abs_hyp i p)
      | abs_hyp i (ZAbsP (x, t, p)) = ZAbsP (x, t, abs_hyp (i + 1) p)
      | abs_hyp i (ZAppt (p, t)) = ZAppt (abs_hyp i p, t)
      | abs_hyp i (ZAppP (p, q)) = ZAppP (abs_hyp i p, abs_hyp i q)
      | abs_hyp _ p = p;
  in ZAbsP ("H", h, abs_hyp 0 prf) end;

fun forall_intr_proof thy (a, x) T prf =
  let
    val z = global_zterm_of thy x;
    val Z = ztyp_of T;

    fun abs_term i b =
      if aconv_zterm (b, z) then ZBound i
      else
        (case b of
          ZAbs (x, T, t) => ZAbs (x, T, abs_term (i + 1) t)
        | ZApp (t, u) => ZApp (abs_term i t, abs_term i u)
        | _ => b);

    fun abd_proof i (ZAbst (x, T, prf)) = ZAbst (x, T, abd_proof (i + 1) prf)
      | abd_proof i (ZAbsP (x, t, prf)) = ZAbsP (x, abs_term i t, abd_proof i prf)
      | abd_proof i (ZAppt (p, t)) = ZAppt (abd_proof i p, abs_term i t)
      | abd_proof i (ZAppP (p, q)) = ZAppP (abd_proof i p, abd_proof i q)
      | abd_proof _ p = p;

  in ZAbst (a, Z, abd_proof 0 prf) end;

fun forall_elim_proof thy t p = ZAppt (p, global_zterm_of thy t);

end;
