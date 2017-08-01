(*  Title:      Tools/Argo/argo_expr.ML
    Author:     Sascha Boehme

The input language of the Argo solver.
*)

signature ARGO_EXPR =
sig
  (* data types *)
  datatype typ = Bool | Real | Func of typ * typ | Type of string
  datatype kind =
    True | False | Not | And | Or | Imp | Iff | Ite | Eq | App | Con of string * typ |
    Le | Lt | Num of Rat.rat | Neg | Add | Sub | Mul | Div | Min | Max | Abs
  datatype expr = E of kind * expr list

  (* indices, equalities, orders *)
  val int_of_kind: kind -> int
  val con_ord: (string * typ) * (string * typ) -> order
  val eq_kind: kind * kind -> bool
  val kind_ord: kind * kind -> order
  val eq_expr: expr * expr -> bool
  val expr_ord: expr * expr -> order
  val dual_expr: expr -> expr -> bool

  (* constructors *)
  val kind_of_string: string -> kind
  val true_expr: expr
  val false_expr: expr
  val mk_not: expr -> expr
  val mk_and: expr list -> expr
  val mk_and2: expr -> expr -> expr
  val mk_or: expr list -> expr
  val mk_or2: expr -> expr -> expr
  val mk_imp: expr -> expr -> expr
  val mk_iff: expr -> expr -> expr
  val mk_ite: expr -> expr -> expr -> expr
  val mk_eq: expr -> expr -> expr
  val mk_app: expr -> expr -> expr
  val mk_con: string * typ -> expr
  val mk_le: expr -> expr -> expr
  val mk_lt: expr -> expr -> expr
  val mk_num: Rat.rat -> expr
  val mk_neg: expr -> expr
  val mk_add: expr list -> expr
  val mk_add2: expr -> expr -> expr
  val mk_sub: expr -> expr -> expr
  val mk_mul: expr -> expr -> expr
  val mk_div: expr -> expr -> expr
  val mk_min: expr -> expr -> expr
  val mk_max: expr -> expr -> expr
  val mk_abs: expr -> expr

  (* type checking *)
  exception TYPE of expr
  exception EXPR of expr
  val type_of: expr -> typ (* raises EXPR *)
  val check: expr -> bool (* raises TYPE and EXPR *)

  (* testers *)
  val is_nary: kind -> bool

  (* string representations *)
  val string_of_kind: kind -> string
end

structure Argo_Expr: ARGO_EXPR =
struct

(* data types *)

datatype typ = Bool | Real | Func of typ * typ | Type of string

datatype kind =
  True | False | Not | And | Or | Imp | Iff | Ite | Eq | App | Con of string * typ |
  Le | Lt | Num of Rat.rat | Neg | Add | Sub | Mul | Div | Min | Max | Abs

datatype expr = E of kind * expr list


(* indices, equalities, orders *)

fun int_of_type Bool = 0
  | int_of_type Real = 1
  | int_of_type (Func _) = 2
  | int_of_type (Type _) = 3

fun int_of_kind True = 0
  | int_of_kind False = 1
  | int_of_kind Not = 2
  | int_of_kind And = 3
  | int_of_kind Or = 4
  | int_of_kind Imp = 5
  | int_of_kind Iff = 6
  | int_of_kind Ite = 7
  | int_of_kind Eq = 8
  | int_of_kind App = 9
  | int_of_kind (Con _) = 10
  | int_of_kind Le = 11
  | int_of_kind Lt = 12
  | int_of_kind (Num _) = 13
  | int_of_kind Neg = 14
  | int_of_kind Add = 15
  | int_of_kind Sub = 16
  | int_of_kind Mul = 17
  | int_of_kind Div = 18
  | int_of_kind Min = 19
  | int_of_kind Max = 20
  | int_of_kind Abs = 21

fun eq_type (Bool, Bool) = true
  | eq_type (Real, Real) = true
  | eq_type (Func tys1, Func tys2) = eq_pair eq_type eq_type (tys1, tys2)
  | eq_type (Type n1, Type n2) = (n1 = n2)
  | eq_type _ = false

fun type_ord (Bool, Bool) = EQUAL
  | type_ord (Real, Real) = EQUAL
  | type_ord (Type n1, Type n2) = fast_string_ord (n1, n2)
  | type_ord (Func tys1, Func tys2) = prod_ord type_ord type_ord (tys1, tys2)
  | type_ord (ty1, ty2) = int_ord (int_of_type ty1, int_of_type ty2)

fun eq_con cp = eq_pair (op =) eq_type cp
fun con_ord cp = prod_ord fast_string_ord type_ord cp

fun eq_kind (Con c1, Con c2) = eq_con (c1, c2)
  | eq_kind (Num n1, Num n2) = n1 = n2
  | eq_kind (k1, k2) = (k1 = k2)

fun kind_ord (Con c1, Con c2) = con_ord (c1, c2)
  | kind_ord (Num n1, Num n2) = Rat.ord (n1, n2)
  | kind_ord (k1, k2) = int_ord (int_of_kind k1, int_of_kind k2)

fun eq_expr (E e1, E e2) = eq_pair eq_kind (eq_list eq_expr) (e1, e2)
fun expr_ord (E e1, E e2) = prod_ord kind_ord (list_ord expr_ord) (e1, e2)

fun dual_expr (E (Not, [e1])) e2 = eq_expr (e1, e2)
  | dual_expr e1 (E (Not, [e2])) = eq_expr (e1, e2)
  | dual_expr _ _ = false


(* constructors *)

val string_kinds = [
  ("true", True),("false", False), ("not", Not), ("and", And), ("or", Or), ("imp", Imp),
  ("iff", Iff), ("ite", Ite), ("eq", Eq), ("app", App), ("le", Le), ("lt", Lt), ("neg", Neg),
  ("add", Add), ("sub", Sub), ("mul", Mul), ("div", Div), ("min", Min), ("max", Max), ("abs", Abs)]

val kind_of_string = the o Symtab.lookup (Symtab.make string_kinds)

val true_expr = E (True, [])
val false_expr = E (False, [])
fun mk_not e = E (Not, [e])
fun mk_and es = E (And, es)
fun mk_and2 e1 e2 = mk_and [e1, e2]
fun mk_or es = E (Or, es)
fun mk_or2 e1 e2 = mk_or [e1, e2]
fun mk_imp e1 e2 = E (Imp, [e1, e2])
fun mk_iff e1 e2 = E (Iff, [e1, e2])
fun mk_ite e1 e2 e3 = E (Ite, [e1, e2, e3])
fun mk_eq e1 e2 = E (Eq, [e1, e2])
fun mk_app e1 e2 = E (App, [e1, e2])
fun mk_con n = E (Con n, [])
fun mk_le e1 e2 = E (Le, [e1, e2])
fun mk_lt e1 e2 = E (Lt, [e1, e2])
fun mk_num r = E (Num r, [])
fun mk_neg e = E (Neg, [e])
fun mk_add es = E (Add, es)
fun mk_add2 e1 e2 = mk_add [e1, e2]
fun mk_sub e1 e2 = E (Sub, [e1, e2])
fun mk_mul e1 e2 = E (Mul, [e1, e2])
fun mk_div e1 e2 = E (Div, [e1, e2])
fun mk_min e1 e2 = E (Min, [e1, e2])
fun mk_max e1 e2 = E (Max, [e1, e2])
fun mk_abs e = E (Abs, [e])


(* type checking *)

exception TYPE of expr
exception EXPR of expr

fun dest_func_type _ (Func tys) = tys
  | dest_func_type e _ = raise TYPE e

fun type_of (E (True, _)) = Bool
  | type_of (E (False, _)) = Bool
  | type_of (E (Not, _)) = Bool
  | type_of (E (And, _)) = Bool
  | type_of (E (Or, _)) = Bool
  | type_of (E (Imp, _)) = Bool
  | type_of (E (Iff, _)) = Bool
  | type_of (E (Ite, [_, e, _])) = type_of e
  | type_of (E (Eq, _)) = Bool
  | type_of (E (App, [e, _])) = snd (dest_func_type e (type_of e))
  | type_of (E (Con (_, ty), _)) = ty
  | type_of (E (Le, _)) = Bool
  | type_of (E (Lt, _)) = Bool
  | type_of (E (Num _, _)) = Real
  | type_of (E (Neg, _)) = Real
  | type_of (E (Add, _)) = Real
  | type_of (E (Sub, _)) = Real
  | type_of (E (Mul, _)) = Real
  | type_of (E (Div, _)) = Real
  | type_of (E (Min, _)) = Real
  | type_of (E (Max, _)) = Real
  | type_of (E (Abs, _)) = Real
  | type_of e = raise EXPR e

fun all_type ty (E (_, es)) = forall (curry eq_type ty o type_of) es
val all_bool = all_type Bool
val all_real = all_type Real

(*
  Types as well as proper arities are checked.
  Exception TYPE is raised for invalid types.
  Exception EXPR is raised for invalid expressions and invalid arities.
*)

fun check (e as E (_, es)) = (forall check es andalso raw_check e) orelse raise TYPE e

and raw_check (E (True, [])) = true
  | raw_check (E (False, [])) = true
  | raw_check (e as E (Not, [_])) = all_bool e
  | raw_check (e as E (And, _ :: _)) = all_bool e
  | raw_check (e as E (Or, _ :: _)) = all_bool e
  | raw_check (e as E (Imp, [_, _])) = all_bool e
  | raw_check (e as E (Iff, [_, _])) = all_bool e
  | raw_check (E (Ite, [e1, e2, e3])) =
      let val ty1 = type_of e1 and ty2 = type_of e2 and ty3 = type_of e3
      in eq_type (ty1, Bool) andalso eq_type (ty2, ty3) end
  | raw_check (E (Eq, [e1, e2])) =
      let val ty1 = type_of e1 and ty2 = type_of e2
      in eq_type (ty1, ty2) andalso not (eq_type (ty1, Bool)) end
  | raw_check (E (App, [e1, e2])) =
      eq_type (fst (dest_func_type e1 (type_of e1)), type_of e2)
  | raw_check (E (Con _, [])) = true
  | raw_check (E (Num _, [])) = true
  | raw_check (e as E (Le, [_, _])) = all_real e
  | raw_check (e as E (Lt, [_, _])) = all_real e
  | raw_check (e as E (Neg, [_])) = all_real e
  | raw_check (e as E (Add, _)) = all_real e
  | raw_check (e as E (Sub, [_, _])) = all_real e
  | raw_check (e as E (Mul, [_, _])) = all_real e
  | raw_check (e as E (Div, [_, _])) = all_real e
  | raw_check (e as E (Min, [_, _])) = all_real e
  | raw_check (e as E (Max, [_, _])) = all_real e
  | raw_check (e as E (Abs, [_])) = all_real e
  | raw_check e = raise EXPR e


(* testers *)

fun is_nary k = member (op =) [And, Or, Add] k


(* string representations *)

val kind_strings = map swap string_kinds

fun string_of_kind (Con (n, _)) = n
  | string_of_kind (Num n) = Rat.string_of_rat n
  | string_of_kind k = the (AList.lookup (op =) kind_strings k)

end

structure Argo_Exprtab = Table(type key = Argo_Expr.expr val ord = Argo_Expr.expr_ord)
