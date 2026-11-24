(*  Title:      Pure/pure_logic.ML
    Author:     Makarius

The pure logic behind Isabelle/Pure: basic datatypes for term language.
*)

signature BASIC_PURE_TERM =
sig
  datatype T =
      TV of indexname * sort
    | FUN of T * T
    | PROP
    | CON0 of string
    | CON1 of string * T
    | CONN of string * T list
  datatype t =
      FV of indexname * T
    | BV of int
    | CONST0 of string
    | CONST1 of string * T
    | CONSTN of string * T list
    | ABS of string * T * t
    | APP of t * t
    | OFCLASS of T * class
end

signature PURE_TERM =
sig
  include BASIC_PURE_TERM
  val FUNs: T list * T -> T
  val fold_tvars: (indexname * sort -> 'a -> 'a) -> T -> 'a -> 'a
  val fold_aterms: (t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_vars: (indexname * T -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_types: (T -> 'a -> 'a) -> t -> 'a -> 'a
  val map_tvars_same: (indexname * sort -> T) -> T Same.operation
  val map_tvars: (indexname * sort -> T) -> T -> T
  val map_aterms_same: t Same.operation -> t Same.operation
  val map_aterms: (t -> t) -> t -> t
  val map_vars_same: (indexname * T -> t) -> t Same.operation
  val map_vars: (indexname * T -> t) -> t -> t
  val map_types_same: T Same.operation -> t Same.operation
  val map_types: (T -> T) -> t -> t
  val type_ord: T ord
  val fast_term_ord: t ord
  val alpha_eq: t * t -> bool
end;

structure Pure_Term: PURE_TERM =
struct

(* datatypes *)

datatype T =  (* type *)
    TV of indexname * sort
  | FUN of T * T
  | PROP
  | CON0 of string             (*type constant*)
  | CON1 of string * T         (*type constructor: 1 type argument*)
  | CONN of string * T list    (*type constructor: >= 2 type arguments*)

datatype t =  (* term *)
    FV of indexname * T
  | BV of int
  | CONST0 of string           (*monomorphic term constant*)
  | CONST1 of string * T       (*polymorphic term constant: 1 type argument*)
  | CONSTN of string * T list  (*polymorphic term constant: >= 2 type arguments*)
  | ABS of string * T * t
  | APP of t * t
  | OFCLASS of T * class

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

fun type_ord TU =
  if pointer_eq TU then EQUAL
  else
    (case TU of
      (TV (a, A), TV (b, B)) =>
        (case fast_indexname_ord (a, b) of EQUAL => sort_ord (A, B) | ord => ord)
    | (FUN (T, T'), FUN (U, U')) =>
        (case type_ord (T, U) of EQUAL => type_ord (T', U') | ord => ord)
    | (PROP, PROP) => EQUAL
    | (CON0 a, CON0 b) => fast_string_ord (a, b)
    | (CON1 (a, T), CON1 (b, U)) =>
        (case fast_string_ord (a, b) of EQUAL => type_ord (T, U) | ord => ord)
    | (CONN (a, Ts), CONN (b, Us)) =>
        (case fast_string_ord (a, b) of EQUAL => dict_ord type_ord (Ts, Us) | ord => ord)
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
        (case type_ord (T, U) of EQUAL => types_ord (t, u) | ord => ord)
    | (APP (t1, t2), APP (u1, u2)) =>
        (case types_ord (t1, u1) of EQUAL => types_ord (t2, u2) | ord => ord)
    | (CONST1 (_, T), CONST1 (_, U)) => type_ord (T, U)
    | (CONSTN (_, Ts), CONSTN (_, Us)) => dict_ord type_ord (Ts, Us)
    | (FV (_, T), FV (_, U)) => type_ord (T, U)
    | (OFCLASS (T, _), OFCLASS (U, _)) => type_ord (T, U)
    | _ => EQUAL);

in

val fast_term_ord = struct_ord ||| atoms_ord ||| types_ord;

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

structure Pure_Types = Table(type key = Pure_Term.T val ord = Pure_Term.type_ord);
structure Pure_Terms = Table(type key = Pure_Term.t val ord = Pure_Term.fast_term_ord);

structure Pure_TVars:
sig
  include TERM_ITEMS
  val add_tvarsT: Pure_Term.T -> set -> set
  val add_tvars: Pure_Term.t -> set -> set
end =
struct
  open TVars;
  val add_tvarsT = Pure_Term.fold_tvars add_set;
  val add_tvars = Pure_Term.fold_types add_tvarsT;
end;

structure Pure_Vars:
sig
  include TERM_ITEMS
  val add_vars: Pure_Term.t -> set -> set
end =
struct

structure Term_Items = Term_Items
(
  type key = indexname * Pure_Term.T;
  val ord = pointer_eq_ord (prod_ord Term_Ord.fast_indexname_ord Pure_Term.type_ord);
);
open Term_Items;

val add_vars = Pure_Term.fold_vars add_set;

end;
