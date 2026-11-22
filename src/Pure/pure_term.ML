(*  Title:      Pure/pure_logic.ML
    Author:     Makarius

The pure logic behind Isabelle/Pure: basic datatypes for term language.
*)

(* types and terms *)

datatype ztyp =
    ZTVar of indexname * sort      (*free: index ~1*)
  | ZFun of ztyp * ztyp
  | ZProp
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
  | OFCLASS of ztyp * class

structure ZTerm =
struct

(* fold *)

fun fold_tvars f (ZTVar v) acc = acc |> f v
  | fold_tvars f (ZFun (T, U)) acc = acc |> fold_tvars f T |> fold_tvars f U
  | fold_tvars f (ZType1 (_, T)) acc = acc |> fold_tvars f T
  | fold_tvars f (ZType (_, Ts)) acc = acc |> fold (fold_tvars f) Ts
  | fold_tvars _ _ acc = acc;

fun fold_aterms f (ZApp (t, u)) acc = acc |> fold_aterms f t |> fold_aterms f u
  | fold_aterms f (ZAbs (_, _, t)) acc = acc |> fold_aterms f t
  | fold_aterms f a acc = acc |> f a;

fun fold_vars f = fold_aterms (fn ZVar v => f v | _ => I);

fun fold_types f (ZVar (_, T)) acc = acc |> f T
  | fold_types f (ZConst1 (_, T)) acc = acc |> f T
  | fold_types f (ZConst (_, As)) acc = acc |> fold f As
  | fold_types f (ZAbs (_, T, b)) acc = acc |> f T |> fold_types f b
  | fold_types f (ZApp (t, u)) acc = acc |> fold_types f t |> fold_types f u
  | fold_types f (OFCLASS (T, _)) acc = acc |> f T
  | fold_types _ _ acc = acc;


(* map *)

fun map_tvars_same f =
  let
    fun typ (ZTVar v) = f v
      | typ (ZFun (T, U)) =
          (ZFun (typ T, Same.commit typ U)
            handle Same.SAME => ZFun (T, typ U))
      | typ ZProp = raise Same.SAME
      | typ (ZType0 _) = raise Same.SAME
      | typ (ZType1 (a, T)) = ZType1 (a, typ T)
      | typ (ZType (a, Ts)) = ZType (a, Same.map typ Ts);
  in typ end;

fun map_aterms_same f =
  let
    fun term (ZAbs (x, T, t)) = ZAbs (x, T, term t)
      | term (ZApp (t, u)) =
          (ZApp (term t, Same.commit term u)
            handle Same.SAME => ZApp (t, term u))
      | term a = f a;
  in term end;

fun map_vars_same f = map_aterms_same (fn ZVar v => f v | _ => raise Same.SAME);

fun map_types_same f =
  let
    fun term (ZVar (xi, T)) = ZVar (xi, f T)
      | term (ZBound _) = raise Same.SAME
      | term (ZConst0 _) = raise Same.SAME
      | term (ZConst1 (c, T)) = ZConst1 (c, f T)
      | term (ZConst (c, Ts)) = ZConst (c, Same.map f Ts)
      | term (ZAbs (x, T, t)) =
          (ZAbs (x, f T, Same.commit term t)
            handle Same.SAME => ZAbs (x, T, term t))
      | term (ZApp (t, u)) =
          (ZApp (term t, Same.commit term u)
            handle Same.SAME => ZApp (t, term u))
      | term (OFCLASS (T, c)) = OFCLASS (f T, c);
  in term end;

val map_tvars = Same.commit o map_tvars_same;
val map_aterms = Same.commit o map_aterms_same;
val map_vars = Same.commit o map_vars_same;
val map_types = Same.commit o map_types_same;


(* type ordering *)

local

fun cons_nr (ZTVar _) = 0
  | cons_nr (ZFun _) = 1
  | cons_nr ZProp = 2
  | cons_nr (ZType0 _) = 3
  | cons_nr (ZType1 _) = 4
  | cons_nr (ZType _) = 5;

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
    | (ZType0 a, ZType0 b) => fast_string_ord (a, b)
    | (ZType1 (a, T), ZType1 (b, U)) =>
        (case fast_string_ord (a, b) of EQUAL => ztyp_ord (T, U) | ord => ord)
    | (ZType (a, Ts), ZType (b, Us)) =>
        (case fast_string_ord (a, b) of EQUAL => dict_ord ztyp_ord (Ts, Us) | ord => ord)
    | (T, U) => int_ord (cons_nr T, cons_nr U));

end;


(* term ordering and alpha-conversion *)

local

fun cons_nr (ZVar _) = 0
  | cons_nr (ZBound _) = 1
  | cons_nr (ZConst0 _) = 2
  | cons_nr (ZConst1 _) = 3
  | cons_nr (ZConst _) = 4
  | cons_nr (ZAbs _) = 5
  | cons_nr (ZApp _) = 6
  | cons_nr (OFCLASS _) = 7;

fun struct_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (ZAbs (_, _, t), ZAbs (_, _, u)) => struct_ord (t, u)
    | (ZApp (t1, t2), ZApp (u1, u2)) =>
        (case struct_ord (t1, u1) of EQUAL => struct_ord (t2, u2) | ord => ord)
    | (t, u) => int_ord (cons_nr t, cons_nr u));

fun atoms_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (ZAbs (_, _, t), ZAbs (_, _, u)) => atoms_ord (t, u)
    | (ZApp (t1, t2), ZApp (u1, u2)) =>
        (case atoms_ord (t1, u1) of EQUAL => atoms_ord (t2, u2) | ord => ord)
    | (ZConst0 a, ZConst0 b) => fast_string_ord (a, b)
    | (ZConst1 (a, _), ZConst1 (b, _)) => fast_string_ord (a, b)
    | (ZConst (a, _), ZConst (b, _)) => fast_string_ord (a, b)
    | (ZVar (xi, _), ZVar (yj, _)) => Term_Ord.fast_indexname_ord (xi, yj)
    | (ZBound i, ZBound j) => int_ord (i, j)
    | (OFCLASS (_, a), OFCLASS (_, b)) => fast_string_ord (a, b)
    | _ => EQUAL);

fun types_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (ZAbs (_, T, t), ZAbs (_, U, u)) =>
        (case ztyp_ord (T, U) of EQUAL => types_ord (t, u) | ord => ord)
    | (ZApp (t1, t2), ZApp (u1, u2)) =>
        (case types_ord (t1, u1) of EQUAL => types_ord (t2, u2) | ord => ord)
    | (ZConst1 (_, T), ZConst1 (_, U)) => ztyp_ord (T, U)
    | (ZConst (_, Ts), ZConst (_, Us)) => dict_ord ztyp_ord (Ts, Us)
    | (ZVar (_, T), ZVar (_, U)) => ztyp_ord (T, U)
    | (OFCLASS (T, _), OFCLASS (U, _)) => ztyp_ord (T, U)
    | _ => EQUAL);

in

val fast_zterm_ord = struct_ord ||| atoms_ord ||| types_ord;

end;

fun aconv_zterm (tm1, tm2) =
  pointer_eq (tm1, tm2) orelse
    (case (tm1, tm2) of
      (ZApp (t1, u1), ZApp (t2, u2)) => aconv_zterm (t1, t2) andalso aconv_zterm (u1, u2)
    | (ZAbs (_, T1, t1), ZAbs (_, T2, t2)) => aconv_zterm (t1, t2) andalso T1 = T2
    | (a1, a2) => a1 = a2);

end;


(* tables and term items *)

structure ZTypes = Table(type key = ztyp val ord = ZTerm.ztyp_ord);
structure ZTerms = Table(type key = zterm val ord = ZTerm.fast_zterm_ord);

structure ZTVars:
sig
  include TERM_ITEMS
  val add_tvarsT: ztyp -> set -> set
  val add_tvars: zterm -> set -> set
end =
struct
  open TVars;
  val add_tvarsT = ZTerm.fold_tvars add_set;
  val add_tvars = ZTerm.fold_types add_tvarsT;
end;

structure ZVars:
sig
  include TERM_ITEMS
  val add_vars: zterm -> set -> set
end =
struct

structure Term_Items = Term_Items
(
  type key = indexname * ztyp;
  val ord = pointer_eq_ord (prod_ord Term_Ord.fast_indexname_ord ZTerm.ztyp_ord);
);
open Term_Items;

val add_vars = ZTerm.fold_vars add_set;

end;
