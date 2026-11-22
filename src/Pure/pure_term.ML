(*  Title:      Pure/pure_logic.ML
    Author:     Makarius

The pure logic behind Isabelle/Pure: basic datatypes for term language.
*)

signature BASIC_PURE_TERM =
sig
  datatype ztyp =
      TV of indexname * sort
    | FUN of ztyp * ztyp
    | PROP
    | CON0 of string
    | CON1 of string * ztyp
    | CONN of string * ztyp list
  datatype zterm =
      FV of indexname * ztyp
    | BV of int
    | CONST0 of string
    | CONST1 of string * ztyp
    | CONSTN of string * ztyp list
    | ABS of string * ztyp * zterm
    | APP of zterm * zterm
    | OFCLASS of ztyp * class
end

signature PURE_TERM =
sig
  include BASIC_PURE_TERM
  val FUNs: ztyp list * ztyp -> ztyp
  val fold_tvars: (indexname * sort -> 'a -> 'a) -> ztyp -> 'a -> 'a
  val fold_aterms: (zterm -> 'a -> 'a) -> zterm -> 'a -> 'a
  val fold_vars: (indexname * ztyp -> 'a -> 'a) -> zterm -> 'a -> 'a
  val fold_types: (ztyp -> 'a -> 'a) -> zterm -> 'a -> 'a
  val map_tvars_same: (indexname * sort -> ztyp) -> ztyp Same.operation
  val map_tvars: (indexname * sort -> ztyp) -> ztyp -> ztyp
  val map_aterms_same: zterm Same.operation -> zterm Same.operation
  val map_aterms: (zterm -> zterm) -> zterm -> zterm
  val map_vars_same: (indexname * ztyp -> zterm) -> zterm Same.operation
  val map_vars: (indexname * ztyp -> zterm) -> zterm -> zterm
  val map_types_same: ztyp Same.operation -> zterm Same.operation
  val map_types: (ztyp -> ztyp) -> zterm -> zterm
  val ztyp_ord: ztyp ord
  val fast_zterm_ord: zterm ord
  val alpha_eq: zterm * zterm -> bool
end;

structure Pure_Term: PURE_TERM =
struct

(* datatypes *)

datatype ztyp =
    TV of indexname * sort        (*free: index ~1*)
  | FUN of ztyp * ztyp
  | PROP
  | CON0 of string                (*type constant*)
  | CON1 of string * ztyp         (*type constructor: 1 argument*)
  | CONN of string * ztyp list    (*type constructor: >= 2 arguments*)

datatype zterm =
    FV of indexname * ztyp        (*free: index ~1*)
  | BV of int
  | CONST0 of string              (*monomorphic constant*)
  | CONST1 of string * ztyp       (*polymorphic constant: 1 type argument*)
  | CONSTN of string * ztyp list  (*polymorphic constant: >= 2 type arguments*)
  | ABS of string * ztyp * zterm
  | APP of zterm * zterm
  | OFCLASS of ztyp * class

val FUNs = Library.foldr FUN;


(* fold *)

fun fold_tvars f (TV v) acc = acc |> f v
  | fold_tvars f (FUN (T, U)) acc = acc |> fold_tvars f T |> fold_tvars f U
  | fold_tvars f (CON1 (_, T)) acc = acc |> fold_tvars f T
  | fold_tvars f (CONN (_, Ts)) acc = acc |> fold (fold_tvars f) Ts
  | fold_tvars _ _ acc = acc;

fun fold_aterms f (APP (t, u)) acc = acc |> fold_aterms f t |> fold_aterms f u
  | fold_aterms f (ABS (_, _, t)) acc = acc |> fold_aterms f t
  | fold_aterms f a acc = acc |> f a;

fun fold_vars f = fold_aterms (fn FV v => f v | _ => I);

fun fold_types f (FV (_, T)) acc = acc |> f T
  | fold_types f (CONST1 (_, T)) acc = acc |> f T
  | fold_types f (CONSTN (_, As)) acc = acc |> fold f As
  | fold_types f (ABS (_, T, b)) acc = acc |> f T |> fold_types f b
  | fold_types f (APP (t, u)) acc = acc |> fold_types f t |> fold_types f u
  | fold_types f (OFCLASS (T, _)) acc = acc |> f T
  | fold_types _ _ acc = acc;


(* map *)

fun map_tvars_same f =
  let
    fun typ (TV v) = f v
      | typ (FUN (T, U)) =
          (FUN (typ T, Same.commit typ U)
            handle Same.SAME => FUN (T, typ U))
      | typ PROP = raise Same.SAME
      | typ (CON0 _) = raise Same.SAME
      | typ (CON1 (a, T)) = CON1 (a, typ T)
      | typ (CONN (a, Ts)) = CONN (a, Same.map typ Ts);
  in typ end;

fun map_aterms_same f =
  let
    fun term (ABS (x, T, t)) = ABS (x, T, term t)
      | term (APP (t, u)) =
          (APP (term t, Same.commit term u)
            handle Same.SAME => APP (t, term u))
      | term a = f a;
  in term end;

fun map_vars_same f = map_aterms_same (fn FV v => f v | _ => raise Same.SAME);

fun map_types_same f =
  let
    fun term (FV (xi, T)) = FV (xi, f T)
      | term (BV _) = raise Same.SAME
      | term (CONST0 _) = raise Same.SAME
      | term (CONST1 (c, T)) = CONST1 (c, f T)
      | term (CONSTN (c, Ts)) = CONSTN (c, Same.map f Ts)
      | term (ABS (x, T, t)) =
          (ABS (x, f T, Same.commit term t)
            handle Same.SAME => ABS (x, T, term t))
      | term (APP (t, u)) =
          (APP (term t, Same.commit term u)
            handle Same.SAME => APP (t, term u))
      | term (OFCLASS (T, c)) = OFCLASS (f T, c);
  in term end;

val map_tvars = Same.commit o map_tvars_same;
val map_aterms = Same.commit o map_aterms_same;
val map_vars = Same.commit o map_vars_same;
val map_types = Same.commit o map_types_same;


(* type ordering *)

local

fun cons_nr (TV _) = 0
  | cons_nr (FUN _) = 1
  | cons_nr PROP = 2
  | cons_nr (CON0 _) = 3
  | cons_nr (CON1 _) = 4
  | cons_nr (CONN _) = 5;

val fast_indexname_ord = Term_Ord.fast_indexname_ord;
val sort_ord = Term_Ord.sort_ord;

in

fun ztyp_ord TU =
  if pointer_eq TU then EQUAL
  else
    (case TU of
      (TV (a, A), TV (b, B)) =>
        (case fast_indexname_ord (a, b) of EQUAL => sort_ord (A, B) | ord => ord)
    | (FUN (T, T'), FUN (U, U')) =>
        (case ztyp_ord (T, U) of EQUAL => ztyp_ord (T', U') | ord => ord)
    | (PROP, PROP) => EQUAL
    | (CON0 a, CON0 b) => fast_string_ord (a, b)
    | (CON1 (a, T), CON1 (b, U)) =>
        (case fast_string_ord (a, b) of EQUAL => ztyp_ord (T, U) | ord => ord)
    | (CONN (a, Ts), CONN (b, Us)) =>
        (case fast_string_ord (a, b) of EQUAL => dict_ord ztyp_ord (Ts, Us) | ord => ord)
    | (T, U) => int_ord (cons_nr T, cons_nr U));

end;


(* term ordering and alpha-conversion *)

local

fun cons_nr (FV _) = 0
  | cons_nr (BV _) = 1
  | cons_nr (CONST0 _) = 2
  | cons_nr (CONST1 _) = 3
  | cons_nr (CONSTN _) = 4
  | cons_nr (ABS _) = 5
  | cons_nr (APP _) = 6
  | cons_nr (OFCLASS _) = 7;

fun struct_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (ABS (_, _, t), ABS (_, _, u)) => struct_ord (t, u)
    | (APP (t1, t2), APP (u1, u2)) =>
        (case struct_ord (t1, u1) of EQUAL => struct_ord (t2, u2) | ord => ord)
    | (t, u) => int_ord (cons_nr t, cons_nr u));

fun atoms_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (ABS (_, _, t), ABS (_, _, u)) => atoms_ord (t, u)
    | (APP (t1, t2), APP (u1, u2)) =>
        (case atoms_ord (t1, u1) of EQUAL => atoms_ord (t2, u2) | ord => ord)
    | (CONST0 a, CONST0 b) => fast_string_ord (a, b)
    | (CONST1 (a, _), CONST1 (b, _)) => fast_string_ord (a, b)
    | (CONSTN (a, _), CONSTN (b, _)) => fast_string_ord (a, b)
    | (FV (xi, _), FV (yj, _)) => Term_Ord.fast_indexname_ord (xi, yj)
    | (BV i, BV j) => int_ord (i, j)
    | (OFCLASS (_, a), OFCLASS (_, b)) => fast_string_ord (a, b)
    | _ => EQUAL);

fun types_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (ABS (_, T, t), ABS (_, U, u)) =>
        (case ztyp_ord (T, U) of EQUAL => types_ord (t, u) | ord => ord)
    | (APP (t1, t2), APP (u1, u2)) =>
        (case types_ord (t1, u1) of EQUAL => types_ord (t2, u2) | ord => ord)
    | (CONST1 (_, T), CONST1 (_, U)) => ztyp_ord (T, U)
    | (CONSTN (_, Ts), CONSTN (_, Us)) => dict_ord ztyp_ord (Ts, Us)
    | (FV (_, T), FV (_, U)) => ztyp_ord (T, U)
    | (OFCLASS (T, _), OFCLASS (U, _)) => ztyp_ord (T, U)
    | _ => EQUAL);

in

val fast_zterm_ord = struct_ord ||| atoms_ord ||| types_ord;

end;

fun alpha_eq (tm1, tm2) =
  pointer_eq (tm1, tm2) orelse
    (case (tm1, tm2) of
      (APP (t1, u1), APP (t2, u2)) => alpha_eq (t1, t2) andalso alpha_eq (u1, u2)
    | (ABS (_, T1, t1), ABS (_, T2, t2)) => alpha_eq (t1, t2) andalso T1 = T2
    | (a1, a2) => a1 = a2);

end;

structure Basic_Pure_Term: BASIC_PURE_TERM = Pure_Term;


(* tables and term items *)

structure ZTypes = Table(type key = Pure_Term.ztyp val ord = Pure_Term.ztyp_ord);
structure ZTerms = Table(type key = Pure_Term.zterm val ord = Pure_Term.fast_zterm_ord);

structure ZTVars:
sig
  include TERM_ITEMS
  val add_tvarsT: Pure_Term.ztyp -> set -> set
  val add_tvars: Pure_Term.zterm -> set -> set
end =
struct
  open TVars;
  val add_tvarsT = Pure_Term.fold_tvars add_set;
  val add_tvars = Pure_Term.fold_types add_tvarsT;
end;

structure ZVars:
sig
  include TERM_ITEMS
  val add_vars: Pure_Term.zterm -> set -> set
end =
struct

structure Term_Items = Term_Items
(
  type key = indexname * Pure_Term.ztyp;
  val ord = pointer_eq_ord (prod_ord Term_Ord.fast_indexname_ord Pure_Term.ztyp_ord);
);
open Term_Items;

val add_vars = Pure_Term.fold_vars add_set;

end;
