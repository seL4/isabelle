(*  Title:      Pure/zterm.ML
    Author:     Makarius

Tight representation of types / terms / proof terms, notably for proof recording.
*)

(* global datatypes *)

datatype ztyp =
    ZTFree of string * sort
  | ZTVar of indexname * sort
  | ZFun of ztyp * ztyp
  | ZProp
  | ZItself of ztyp
  | ZType0 of string               (*type constant*)
  | ZType1 of string * ztyp        (*type constructor: 1 argument*)
  | ZType of string * ztyp list    (*type constructor: >= 2 arguments*)

datatype zterm =
    ZFree of string * ztyp
  | ZVar of indexname * ztyp
  | ZBound of int
  | ZConst0 of string              (*monomorphic constant*)
  | ZConst1 of string * ztyp       (*polymorphic constant: 1 type argument*)
  | ZConst of string * ztyp list   (*polymorphic constant: >= 2 type arguments*)
  | ZAbs of string * ztyp * zterm
  | ZApp of zterm * zterm
  | ZClass of ztyp * class         (*OFCLASS proposition*)

datatype zproof =
    ZDummy                         (*dummy proof*)
  | ZConstP of serial * ztyp list  (*proof constant: local box, global axiom or thm*)
  | ZBoundP of int
  | ZHyp of zterm
  | ZAbst of string * ztyp * zproof
  | ZAbsP of string * zterm * zproof
  | ZAppt of zproof * zterm
  | ZAppP of zproof * zproof
  | ZClassP of ztyp * class        (*OFCLASS proof from sorts algebra*)
  | ZOracle of serial * zterm * ztyp list
and zproof_body = ZPBody of
  {boxes: (zterm * zproof future) Inttab.table,
   consts: serial Ord_List.T,
   oracles: ((string * Position.T) * zterm option) Ord_List.T,
   proof: zproof}


signature ZTERM =
sig
  datatype ztyp = datatype ztyp
  datatype zterm = datatype zterm
  datatype zproof = datatype zproof
  val ztyp_ord: ztyp * ztyp -> order
  val zaconv: zterm * zterm -> bool
  val ztyp_of: typ -> ztyp
  val typ_of: ztyp -> typ
  val zterm_of: Consts.T -> term -> zterm
  val term_of: Consts.T -> zterm -> term
end;

structure ZTerm: ZTERM =
struct

datatype ztyp = datatype ztyp;
datatype zterm = datatype zterm;
datatype zproof = datatype zproof;


(* orderings *)

local

fun cons_nr (ZTFree _) = 0
  | cons_nr (ZTVar _) = 1
  | cons_nr (ZFun _) = 2
  | cons_nr ZProp = 3
  | cons_nr (ZItself _) = 4
  | cons_nr (ZType0 _) = 5
  | cons_nr (ZType1 _) = 6
  | cons_nr (ZType _) = 7;

val fast_indexname_ord = Term_Ord.fast_indexname_ord;
val sort_ord = Term_Ord.sort_ord;

in

fun ztyp_ord TU =
  if pointer_eq TU then EQUAL
  else
    (case TU of
      (ZTFree (a, A), ZTFree (b, B)) =>
        (case fast_string_ord (a, b) of EQUAL => sort_ord (A, B) | ord => ord)
    | (ZTVar (a, A), ZTVar (b, B)) =>
        (case fast_indexname_ord (a, b) of EQUAL => Term_Ord.sort_ord (A, B) | ord => ord)
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

fun zaconv (tm1, tm2) =
  pointer_eq (tm1, tm2) orelse
    (case (tm1, tm2) of
      (ZApp (t1, u1), ZApp (t2, u2)) => zaconv (t1, t2) andalso zaconv (u1, u2)
    | (ZAbs (_, T1, t1), ZAbs (_, T2, t2)) => zaconv (t1, t2) andalso T1 = T2
    | (a1, a2) => a1 = a2);


(* convert ztyp / zterm vs. regular typ / term *)

fun ztyp_of (TFree v) = ZTFree v
  | ztyp_of (TVar v) = ZTVar v
  | ztyp_of (Type ("fun", [T, U])) = ZFun (ztyp_of T, ztyp_of U)
  | ztyp_of (Type (c, [])) = if c = "prop" then ZProp else ZType0 c
  | ztyp_of (Type (c, [T])) = if c = "itself" then ZItself (ztyp_of T) else ZType1 (c, ztyp_of T)
  | ztyp_of (Type (c, ts)) = ZType (c, map ztyp_of ts);

fun typ_of (ZTFree v) = TFree v
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
    fun zterm (Free (x, T)) = ZFree (x, ztyp_of T)
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
    fun term (ZFree (x, T)) = Free (x, typ_of T)
      | term (ZVar (xi, T)) = Var (xi, typ_of T)
      | term (ZBound i) = Bound i
      | term (ZConst0 c) = const (c, [])
      | term (ZConst1 (c, T)) = const (c, [typ_of T])
      | term (ZConst (c, Ts)) = const (c, map typ_of Ts)
      | term (ZAbs (a, T, b)) = Abs (a, typ_of T, term b)
      | term (ZApp (t, u)) = term t $ term u
      | term (ZClass (T, c)) = Logic.mk_of_class (typ_of T, c);
  in term end;

end;
