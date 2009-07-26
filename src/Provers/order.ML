(*  Author:     Oliver Kutter, TU Muenchen

Transitivity reasoner for partial and linear orders.
*)

(* TODO: reduce number of input thms *)

(*

The package provides tactics partial_tac and linear_tac that use all
premises of the form

  t = u, t ~= u, t < u, t <= u, ~(t < u) and ~(t <= u)

to
1. either derive a contradiction,
   in which case the conclusion can be any term,
2. or prove the conclusion, which must be of the same form as the
   premises (excluding ~(t < u) and ~(t <= u) for partial orders)

The package is not limited to the relation <= and friends.  It can be
instantiated to any partial and/or linear order --- for example, the
divisibility relation "dvd".  In order to instantiate the package for
a partial order only, supply dummy theorems to the rules for linear
orders, and don't use linear_tac!

*)

signature ORDER_TAC =
sig
  (* Theorems required by the reasoner *)
  type less_arith
  val empty : thm -> less_arith
  val update : string -> thm -> less_arith -> less_arith

  (* Tactics *)
  val partial_tac:
    (theory -> term -> (term * string * term) option) -> less_arith ->
    Proof.context -> thm list -> int -> tactic
  val linear_tac:
    (theory -> term -> (term * string * term) option) -> less_arith ->
    Proof.context -> thm list -> int -> tactic
end;

structure Order_Tac: ORDER_TAC =
struct

(* Record to handle input theorems in a convenient way. *)

type less_arith =
  {
    (* Theorems for partial orders *)
    less_reflE: thm,  (* x < x ==> P *)
    le_refl: thm,  (* x <= x *)
    less_imp_le: thm, (* x < y ==> x <= y *)
    eqI: thm, (* [| x <= y; y <= x |] ==> x = y *)
    eqD1: thm, (* x = y ==> x <= y *)
    eqD2: thm, (* x = y ==> y <= x *)
    less_trans: thm,  (* [| x < y; y < z |] ==> x < z *)
    less_le_trans: thm,  (* [| x < y; y <= z |] ==> x < z *)
    le_less_trans: thm,  (* [| x <= y; y < z |] ==> x < z *)
    le_trans: thm,  (* [| x <= y; y <= z |] ==> x <= z *)
    le_neq_trans : thm, (* [| x <= y ; x ~= y |] ==> x < y *)
    neq_le_trans : thm, (* [| x ~= y ; x <= y |] ==> x < y *)
    not_sym : thm, (* x ~= y ==> y ~= x *)

    (* Additional theorems for linear orders *)
    not_lessD: thm, (* ~(x < y) ==> y <= x *)
    not_leD: thm, (* ~(x <= y) ==> y < x *)
    not_lessI: thm, (* y <= x  ==> ~(x < y) *)
    not_leI: thm, (* y < x  ==> ~(x <= y) *)

    (* Additional theorems for subgoals of form x ~= y *)
    less_imp_neq : thm, (* x < y ==> x ~= y *)
    eq_neq_eq_imp_neq : thm (* [| x = u ; u ~= v ; v = z|] ==> x ~= z *)
  }

fun empty dummy_thm =
    {less_reflE= dummy_thm, le_refl= dummy_thm, less_imp_le= dummy_thm, eqI= dummy_thm,
      eqD1= dummy_thm, eqD2= dummy_thm,
      less_trans= dummy_thm, less_le_trans= dummy_thm, le_less_trans= dummy_thm,
      le_trans= dummy_thm, le_neq_trans = dummy_thm, neq_le_trans = dummy_thm,
      not_sym = dummy_thm,
      not_lessD= dummy_thm, not_leD= dummy_thm, not_lessI= dummy_thm, not_leI= dummy_thm,
      less_imp_neq = dummy_thm, eq_neq_eq_imp_neq = dummy_thm}

fun change thms f =
  let
    val {less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq} = thms;
    val (less_reflE', le_refl', less_imp_le', eqI', eqD1', eqD2', less_trans',
      less_le_trans', le_less_trans', le_trans', le_neq_trans', neq_le_trans',
      not_sym', not_lessD', not_leD', not_lessI', not_leI', less_imp_neq',
      eq_neq_eq_imp_neq') =
     f (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq)
  in {less_reflE = less_reflE', le_refl= le_refl',
      less_imp_le = less_imp_le', eqI = eqI', eqD1 = eqD1', eqD2 = eqD2',
      less_trans = less_trans', less_le_trans = less_le_trans',
      le_less_trans = le_less_trans', le_trans = le_trans', le_neq_trans = le_neq_trans',
      neq_le_trans = neq_le_trans', not_sym = not_sym',
      not_lessD = not_lessD', not_leD = not_leD', not_lessI = not_lessI',
      not_leI = not_leI',
      less_imp_neq = less_imp_neq', eq_neq_eq_imp_neq = eq_neq_eq_imp_neq'}
  end;

fun update "less_reflE" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (thm, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "le_refl" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, thm, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "less_imp_le" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, thm, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "eqI" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, thm, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "eqD1" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, thm, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "eqD2" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, eqD1, thm, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "less_trans" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, thm,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "less_le_trans" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      thm, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "le_less_trans" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, thm, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "le_trans" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, thm, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "le_neq_trans" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, thm, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "neq_le_trans" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, thm,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "not_sym" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      thm, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "not_lessD" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, thm, not_leD, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "not_leD" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, thm, not_lessI, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "not_lessI" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, thm, not_leI, less_imp_neq, eq_neq_eq_imp_neq))
  | update "not_leI" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, thm, less_imp_neq, eq_neq_eq_imp_neq))
  | update "less_imp_neq" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, thm, eq_neq_eq_imp_neq))
  | update "eq_neq_eq_imp_neq" thm thms =
    change thms (fn (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq,
      eq_neq_eq_imp_neq) =>
    (less_reflE, le_refl, less_imp_le, eqI, eqD1, eqD2, less_trans,
      less_le_trans, le_less_trans, le_trans, le_neq_trans, neq_le_trans,
      not_sym, not_lessD, not_leD, not_lessI, not_leI, less_imp_neq, thm));

(* Internal datatype for the proof *)
datatype proof
  = Asm of int
  | Thm of proof list * thm;

exception Cannot;
 (* Internal exception, raised if conclusion cannot be derived from
     assumptions. *)
exception Contr of proof;
  (* Internal exception, raised if contradiction ( x < x ) was derived *)

fun prove asms =
  let fun pr (Asm i) = List.nth (asms, i)
  |       pr (Thm (prfs, thm)) = (map pr prfs) MRS thm
  in pr end;

(* Internal datatype for inequalities *)
datatype less
   = Less  of term * term * proof
   | Le    of term * term * proof
   | NotEq of term * term * proof;

(* Misc functions for datatype less *)
fun lower (Less (x, _, _)) = x
  | lower (Le (x, _, _)) = x
  | lower (NotEq (x,_,_)) = x;

fun upper (Less (_, y, _)) = y
  | upper (Le (_, y, _)) = y
  | upper (NotEq (_,y,_)) = y;

fun getprf   (Less (_, _, p)) = p
|   getprf   (Le   (_, _, p)) = p
|   getprf   (NotEq (_,_, p)) = p;


(* ************************************************************************ *)
(*                                                                          *)
(* mkasm_partial                                                            *)
(*                                                                          *)
(* Tuple (t, n) (t an assumption, n its index in the assumptions) is        *)
(* translated to an element of type less.                                   *)
(* Partial orders only.                                                     *)
(*                                                                          *)
(* ************************************************************************ *)

fun mkasm_partial decomp (less_thms : less_arith) sign (t, n) =
  case decomp sign t of
    SOME (x, rel, y) => (case rel of
      "<"   => if (x aconv y) then raise Contr (Thm ([Asm n], #less_reflE less_thms))
               else [Less (x, y, Asm n)]
    | "~<"  => []
    | "<="  => [Le (x, y, Asm n)]
    | "~<=" => []
    | "="   => [Le (x, y, Thm ([Asm n], #eqD1 less_thms)),
                Le (y, x, Thm ([Asm n], #eqD2 less_thms))]
    | "~="  => if (x aconv y) then
                  raise Contr (Thm ([(Thm ([(Thm ([], #le_refl less_thms)) ,(Asm n)], #le_neq_trans less_thms))], #less_reflE less_thms))
               else [ NotEq (x, y, Asm n),
                      NotEq (y, x,Thm ( [Asm n], #not_sym less_thms))]
    | _     => error ("partial_tac: unknown relation symbol ``" ^ rel ^
                 "''returned by decomp."))
  | NONE => [];

(* ************************************************************************ *)
(*                                                                          *)
(* mkasm_linear                                                             *)
(*                                                                          *)
(* Tuple (t, n) (t an assumption, n its index in the assumptions) is        *)
(* translated to an element of type less.                                   *)
(* Linear orders only.                                                      *)
(*                                                                          *)
(* ************************************************************************ *)

fun mkasm_linear decomp (less_thms : less_arith) sign (t, n) =
  case decomp sign t of
    SOME (x, rel, y) => (case rel of
      "<"   => if (x aconv y) then raise Contr (Thm ([Asm n], #less_reflE less_thms))
               else [Less (x, y, Asm n)]
    | "~<"  => [Le (y, x, Thm ([Asm n], #not_lessD less_thms))]
    | "<="  => [Le (x, y, Asm n)]
    | "~<=" => if (x aconv y) then
                  raise (Contr (Thm ([Thm ([Asm n], #not_leD less_thms)], #less_reflE less_thms)))
               else [Less (y, x, Thm ([Asm n], #not_leD less_thms))]
    | "="   => [Le (x, y, Thm ([Asm n], #eqD1 less_thms)),
                Le (y, x, Thm ([Asm n], #eqD2 less_thms))]
    | "~="  => if (x aconv y) then
                  raise Contr (Thm ([(Thm ([(Thm ([], #le_refl less_thms)) ,(Asm n)], #le_neq_trans less_thms))], #less_reflE less_thms))
               else [ NotEq (x, y, Asm n),
                      NotEq (y, x,Thm ( [Asm n], #not_sym less_thms))]
    | _     => error ("linear_tac: unknown relation symbol ``" ^ rel ^
                 "''returned by decomp."))
  | NONE => [];

(* ************************************************************************ *)
(*                                                                          *)
(* mkconcl_partial                                                          *)
(*                                                                          *)
(* Translates conclusion t to an element of type less.                      *)
(* Partial orders only.                                                     *)
(*                                                                          *)
(* ************************************************************************ *)

fun mkconcl_partial decomp (less_thms : less_arith) sign t =
  case decomp sign t of
    SOME (x, rel, y) => (case rel of
      "<"   => ([Less (x, y, Asm ~1)], Asm 0)
    | "<="  => ([Le (x, y, Asm ~1)], Asm 0)
    | "="   => ([Le (x, y, Asm ~1), Le (y, x, Asm ~1)],
                 Thm ([Asm 0, Asm 1], #eqI less_thms))
    | "~="  => ([NotEq (x,y, Asm ~1)], Asm 0)
    | _  => raise Cannot)
  | NONE => raise Cannot;

(* ************************************************************************ *)
(*                                                                          *)
(* mkconcl_linear                                                           *)
(*                                                                          *)
(* Translates conclusion t to an element of type less.                      *)
(* Linear orders only.                                                      *)
(*                                                                          *)
(* ************************************************************************ *)

fun mkconcl_linear decomp (less_thms : less_arith) sign t =
  case decomp sign t of
    SOME (x, rel, y) => (case rel of
      "<"   => ([Less (x, y, Asm ~1)], Asm 0)
    | "~<"  => ([Le (y, x, Asm ~1)], Thm ([Asm 0], #not_lessI less_thms))
    | "<="  => ([Le (x, y, Asm ~1)], Asm 0)
    | "~<=" => ([Less (y, x, Asm ~1)], Thm ([Asm 0], #not_leI less_thms))
    | "="   => ([Le (x, y, Asm ~1), Le (y, x, Asm ~1)],
                 Thm ([Asm 0, Asm 1], #eqI less_thms))
    | "~="  => ([NotEq (x,y, Asm ~1)], Asm 0)
    | _  => raise Cannot)
  | NONE => raise Cannot;


(*** The common part for partial and linear orders ***)

(* Analysis of premises and conclusion: *)
(* decomp (`x Rel y') should yield (x, Rel, y)
     where Rel is one of "<", "<=", "~<", "~<=", "=" and "~=",
     other relation symbols cause an error message *)

fun gen_order_tac mkasm mkconcl decomp' (less_thms : less_arith) ctxt prems =

let

fun decomp sign t = Option.map (fn (x, rel, y) =>
  (Envir.beta_eta_contract x, rel, Envir.beta_eta_contract y)) (decomp' sign t);

(* ******************************************************************* *)
(*                                                                     *)
(* mergeLess                                                           *)
(*                                                                     *)
(* Merge two elements of type less according to the following rules    *)
(*                                                                     *)
(* x <  y && y <  z ==> x < z                                          *)
(* x <  y && y <= z ==> x < z                                          *)
(* x <= y && y <  z ==> x < z                                          *)
(* x <= y && y <= z ==> x <= z                                         *)
(* x <= y && x ~= y ==> x < y                                          *)
(* x ~= y && x <= y ==> x < y                                          *)
(* x <  y && x ~= y ==> x < y                                          *)
(* x ~= y && x <  y ==> x < y                                          *)
(*                                                                     *)
(* ******************************************************************* *)

fun mergeLess (Less (x, _, p) , Less (_ , z, q)) =
      Less (x, z, Thm ([p,q] , #less_trans less_thms))
|   mergeLess (Less (x, _, p) , Le (_ , z, q)) =
      Less (x, z, Thm ([p,q] , #less_le_trans less_thms))
|   mergeLess (Le (x, _, p) , Less (_ , z, q)) =
      Less (x, z, Thm ([p,q] , #le_less_trans less_thms))
|   mergeLess (Le (x, z, p) , NotEq (x', z', q)) =
      if (x aconv x' andalso z aconv z' )
      then Less (x, z, Thm ([p,q] , #le_neq_trans less_thms))
      else error "linear/partial_tac: internal error le_neq_trans"
|   mergeLess (NotEq (x, z, p) , Le (x' , z', q)) =
      if (x aconv x' andalso z aconv z')
      then Less (x, z, Thm ([p,q] , #neq_le_trans less_thms))
      else error "linear/partial_tac: internal error neq_le_trans"
|   mergeLess (NotEq (x, z, p) , Less (x' , z', q)) =
      if (x aconv x' andalso z aconv z')
      then Less ((x' , z', q))
      else error "linear/partial_tac: internal error neq_less_trans"
|   mergeLess (Less (x, z, p) , NotEq (x', z', q)) =
      if (x aconv x' andalso z aconv z')
      then Less (x, z, p)
      else error "linear/partial_tac: internal error less_neq_trans"
|   mergeLess (Le (x, _, p) , Le (_ , z, q)) =
      Le (x, z, Thm ([p,q] , #le_trans less_thms))
|   mergeLess (_, _) =
      error "linear/partial_tac: internal error: undefined case";


(* ******************************************************************** *)
(* tr checks for valid transitivity step                                *)
(* ******************************************************************** *)

infix tr;
fun (Less (_, y, _)) tr (Le (x', _, _))   = ( y aconv x' )
  | (Le   (_, y, _)) tr (Less (x', _, _)) = ( y aconv x' )
  | (Less (_, y, _)) tr (Less (x', _, _)) = ( y aconv x' )
  | (Le (_, y, _))   tr (Le (x', _, _))   = ( y aconv x' )
  | _ tr _ = false;


(* ******************************************************************* *)
(*                                                                     *)
(* transPath (Lesslist, Less): (less list * less) -> less              *)
(*                                                                     *)
(* If a path represented by a list of elements of type less is found,  *)
(* this needs to be contracted to a single element of type less.       *)
(* Prior to each transitivity step it is checked whether the step is   *)
(* valid.                                                              *)
(*                                                                     *)
(* ******************************************************************* *)

fun transPath ([],lesss) = lesss
|   transPath (x::xs,lesss) =
      if lesss tr x then transPath (xs, mergeLess(lesss,x))
      else error "linear/partial_tac: internal error transpath";

(* ******************************************************************* *)
(*                                                                     *)
(* less1 subsumes less2 : less -> less -> bool                         *)
(*                                                                     *)
(* subsumes checks whether less1 implies less2                         *)
(*                                                                     *)
(* ******************************************************************* *)

infix subsumes;
fun (Less (x, y, _)) subsumes (Le (x', y', _)) =
      (x aconv x' andalso y aconv y')
  | (Less (x, y, _)) subsumes (Less (x', y', _)) =
      (x aconv x' andalso y aconv y')
  | (Le (x, y, _)) subsumes (Le (x', y', _)) =
      (x aconv x' andalso y aconv y')
  | (Less (x, y, _)) subsumes (NotEq (x', y', _)) =
      (x aconv x' andalso y aconv y') orelse (y aconv x' andalso x aconv y')
  | (NotEq (x, y, _)) subsumes (NotEq (x', y', _)) =
      (x aconv x' andalso y aconv y') orelse (y aconv x' andalso x aconv y')
  | (Le _) subsumes (Less _) =
      error "linear/partial_tac: internal error: Le cannot subsume Less"
  | _ subsumes _ = false;

(* ******************************************************************* *)
(*                                                                     *)
(* triv_solv less1 : less ->  proof option                     *)
(*                                                                     *)
(* Solves trivial goal x <= x.                                         *)
(*                                                                     *)
(* ******************************************************************* *)

fun triv_solv (Le (x, x', _)) =
    if x aconv x' then  SOME (Thm ([], #le_refl less_thms))
    else NONE
|   triv_solv _ = NONE;

(* ********************************************************************* *)
(* Graph functions                                                       *)
(* ********************************************************************* *)



(* ******************************************************************* *)
(*                                                                     *)
(* General:                                                            *)
(*                                                                     *)
(* Inequalities are represented by various types of graphs.            *)
(*                                                                     *)
(* 1. (Term.term * (Term.term * less) list) list                       *)
(*    - Graph of this type is generated from the assumptions,          *)
(*      it does contain information on which edge stems from which     *)
(*      assumption.                                                    *)
(*    - Used to compute strongly connected components                  *)
(*    - Used to compute component subgraphs                            *)
(*    - Used for component subgraphs to reconstruct paths in components*)
(*                                                                     *)
(* 2. (int * (int * less) list ) list                                  *)
(*    - Graph of this type is generated from the strong components of  *)
(*      graph of type 1.  It consists of the strong components of      *)
(*      graph 1, where nodes are indices of the components.            *)
(*      Only edges between components are part of this graph.          *)
(*    - Used to reconstruct paths between several components.          *)
(*                                                                     *)
(* ******************************************************************* *)


(* *********************************************************** *)
(* Functions for constructing graphs                           *)
(* *********************************************************** *)

fun addEdge (v,d,[]) = [(v,d)]
|   addEdge (v,d,((u,dl)::el)) = if v aconv u then ((v,d@dl)::el)
    else (u,dl):: (addEdge(v,d,el));

(* ********************************************************************* *)
(*                                                                       *)
(* mkGraphs constructs from a list of objects of type less a graph g,    *)
(* by taking all edges that are candidate for a <=, and a list neqE, by  *)
(* taking all edges that are candiate for a ~=                           *)
(*                                                                       *)
(* ********************************************************************* *)

fun mkGraphs [] = ([],[],[])
|   mkGraphs lessList =
 let

fun buildGraphs ([],leqG,neqG,neqE) = (leqG, neqG, neqE)
|   buildGraphs (l::ls, leqG,neqG, neqE) = case l of
  (Less (x,y,p)) =>
       buildGraphs (ls, addEdge (x,[(y,(Less (x, y, p)))],leqG) ,
                        addEdge (x,[(y,(Less (x, y, p)))],neqG), l::neqE)
| (Le (x,y,p)) =>
      buildGraphs (ls, addEdge (x,[(y,(Le (x, y,p)))],leqG) , neqG, neqE)
| (NotEq  (x,y,p)) =>
      buildGraphs (ls, leqG , addEdge (x,[(y,(NotEq (x, y, p)))],neqG), l::neqE) ;

  in buildGraphs (lessList, [], [], []) end;


(* *********************************************************************** *)
(*                                                                         *)
(* adjacent g u : (''a * 'b list ) list -> ''a -> 'b list                  *)
(*                                                                         *)
(* List of successors of u in graph g                                      *)
(*                                                                         *)
(* *********************************************************************** *)

fun adjacent eq_comp ((v,adj)::el) u =
    if eq_comp (u, v) then adj else adjacent eq_comp el u
|   adjacent _  []  _ = []


(* *********************************************************************** *)
(*                                                                         *)
(* transpose g:                                                            *)
(* (''a * ''a list) list -> (''a * ''a list) list                          *)
(*                                                                         *)
(* Computes transposed graph g' from g                                     *)
(* by reversing all edges u -> v to v -> u                                 *)
(*                                                                         *)
(* *********************************************************************** *)

fun transpose eq_comp g =
  let
   (* Compute list of reversed edges for each adjacency list *)
   fun flip (u,(v,l)::el) = (v,(u,l)) :: flip (u,el)
     | flip (_,nil) = nil

   (* Compute adjacency list for node u from the list of edges
      and return a likewise reduced list of edges.  The list of edges
      is searches for edges starting from u, and these edges are removed. *)
   fun gather (u,(v,w)::el) =
    let
     val (adj,edges) = gather (u,el)
    in
     if eq_comp (u, v) then (w::adj,edges)
     else (adj,(v,w)::edges)
    end
   | gather (_,nil) = (nil,nil)

   (* For every node in the input graph, call gather to find all reachable
      nodes in the list of edges *)
   fun assemble ((u,_)::el) edges =
       let val (adj,edges) = gather (u,edges)
       in (u,adj) :: assemble el edges
       end
     | assemble nil _ = nil

   (* Compute, for each adjacency list, the list with reversed edges,
      and concatenate these lists. *)
   val flipped = List.foldr (op @) nil (map flip g)

 in assemble g flipped end

(* *********************************************************************** *)
(*                                                                         *)
(* scc_term : (term * term list) list -> term list list                    *)
(*                                                                         *)
(* The following is based on the algorithm for finding strongly connected  *)
(* components described in Introduction to Algorithms, by Cormon, Leiserson*)
(* and Rivest, section 23.5. The input G is an adjacency list description  *)
(* of a directed graph. The output is a list of the strongly connected     *)
(* components (each a list of vertices).                                   *)
(*                                                                         *)
(*                                                                         *)
(* *********************************************************************** *)

fun scc_term G =
     let
  (* Ordered list of the vertices that DFS has finished with;
     most recently finished goes at the head. *)
  val finish : term list ref = ref nil

  (* List of vertices which have been visited. *)
  val visited : term list ref = ref nil

  fun been_visited v = exists (fn w => w aconv v) (!visited)

  (* Given the adjacency list rep of a graph (a list of pairs),
     return just the first element of each pair, yielding the
     vertex list. *)
  val members = map (fn (v,_) => v)

  (* Returns the nodes in the DFS tree rooted at u in g *)
  fun dfs_visit g u : term list =
      let
   val _ = visited := u :: !visited
   val descendents =
       List.foldr (fn ((v,l),ds) => if been_visited v then ds
            else v :: dfs_visit g v @ ds)
        nil (adjacent (op aconv) g u)
      in
   finish := u :: !finish;
   descendents
      end
     in

  (* DFS on the graph; apply dfs_visit to each vertex in
     the graph, checking first to make sure the vertex is
     as yet unvisited. *)
  app (fn u => if been_visited u then ()
        else (dfs_visit G u; ()))  (members G);
  visited := nil;

  (* We don't reset finish because its value is used by
     foldl below, and it will never be used again (even
     though dfs_visit will continue to modify it). *)

  (* DFS on the transpose. The vertices returned by
     dfs_visit along with u form a connected component. We
     collect all the connected components together in a
     list, which is what is returned. *)
  Library.foldl (fn (comps,u) =>
      if been_visited u then comps
      else ((u :: dfs_visit (transpose (op aconv) G) u) :: comps))  (nil,(!finish))
end;


(* *********************************************************************** *)
(*                                                                         *)
(* dfs_int_reachable g u:                                                  *)
(* (int * int list) list -> int -> int list                                *)
(*                                                                         *)
(* Computes list of all nodes reachable from u in g.                       *)
(*                                                                         *)
(* *********************************************************************** *)

fun dfs_int_reachable g u =
 let
  (* List of vertices which have been visited. *)
  val visited : int list ref = ref nil

  fun been_visited v = exists (fn w => w = v) (!visited)

  fun dfs_visit g u : int list =
      let
   val _ = visited := u :: !visited
   val descendents =
       List.foldr (fn ((v,l),ds) => if been_visited v then ds
            else v :: dfs_visit g v @ ds)
        nil (adjacent (op =) g u)
   in  descendents end

 in u :: dfs_visit g u end;


fun indexComps components =
    ListPair.map (fn (a,b) => (a,b)) (0 upto (length components -1), components);

fun indexNodes IndexComp =
    List.concat (map (fn (index, comp) => (map (fn v => (v,index)) comp)) IndexComp);

fun getIndex v [] = ~1
|   getIndex v ((v',k)::vs) = if v aconv v' then k else getIndex v vs;



(* *********************************************************************** *)
(*                                                                         *)
(* dfs eq_comp g u v:                                                       *)
(* ('a * 'a -> bool) -> ('a  *( 'a * less) list) list ->                   *)
(* 'a -> 'a -> (bool * ('a * less) list)                                   *)
(*                                                                         *)
(* Depth first search of v from u.                                         *)
(* Returns (true, path(u, v)) if successful, otherwise (false, []).        *)
(*                                                                         *)
(* *********************************************************************** *)

fun dfs eq_comp g u v =
 let
    val pred = ref nil;
    val visited = ref nil;

    fun been_visited v = exists (fn w => eq_comp (w, v)) (!visited)

    fun dfs_visit u' =
    let val _ = visited := u' :: (!visited)

    fun update (x,l) = let val _ = pred := (x,l) ::(!pred) in () end;

    in if been_visited v then ()
    else (app (fn (v',l) => if been_visited v' then () else (
       update (v',l);
       dfs_visit v'; ()) )) (adjacent eq_comp g u')
     end
  in
    dfs_visit u;
    if (been_visited v) then (true, (!pred)) else (false , [])
  end;


(* *********************************************************************** *)
(*                                                                         *)
(* completeTermPath u v g:                                                 *)
(* Term.term -> Term.term -> (Term.term * (Term.term * less) list) list    *)
(* -> less list                                                            *)
(*                                                                         *)
(* Complete the path from u to v in graph g.  Path search is performed     *)
(* with dfs_term g u v.  This yields for each node v' its predecessor u'   *)
(* and the edge u' -> v'.  Allows traversing graph backwards from v and    *)
(* finding the path u -> v.                                                *)
(*                                                                         *)
(* *********************************************************************** *)


fun completeTermPath u v g  =
  let
   val (found, tmp) =  dfs (op aconv) g u v ;
   val pred = map snd tmp;

   fun path x y  =
      let

      (* find predecessor u of node v and the edge u -> v *)

      fun lookup v [] = raise Cannot
      |   lookup v (e::es) = if (upper e) aconv v then e else lookup v es;

      (* traverse path backwards and return list of visited edges *)
      fun rev_path v =
       let val l = lookup v pred
           val u = lower l;
       in
        if u aconv x then [l]
        else (rev_path u) @ [l]
       end
     in rev_path y end;

  in
  if found then (if u aconv v then [(Le (u, v, (Thm ([], #le_refl less_thms))))]
  else path u v ) else raise Cannot
end;


(* *********************************************************************** *)
(*                                                                         *)
(* findProof (sccGraph, neqE, ntc, sccSubgraphs) subgoal:                  *)
(*                                                                         *)
(* (int * (int * less) list) list * less list *  (Term.term * int) list    *)
(* * ((term * (term * less) list) list) list -> Less -> proof              *)
(*                                                                         *)
(* findProof constructs from graphs (sccGraph, sccSubgraphs) and neqE a    *)
(* proof for subgoal.  Raises exception Cannot if this is not possible.    *)
(*                                                                         *)
(* *********************************************************************** *)

fun findProof (sccGraph, neqE, ntc, sccSubgraphs) subgoal =
let

 (* complete path x y from component graph *)
 fun completeComponentPath x y predlist =
   let
          val xi = getIndex x ntc
          val yi = getIndex y ntc

          fun lookup k [] =  raise Cannot
          |   lookup k ((h: int,l)::us) = if k = h then l else lookup k us;

          fun rev_completeComponentPath y' =
           let val edge = lookup (getIndex y' ntc) predlist
               val u = lower edge
               val v = upper edge
           in
             if (getIndex u ntc) = xi then
               (completeTermPath x u (List.nth(sccSubgraphs, xi)) )@[edge]
               @(completeTermPath v y' (List.nth(sccSubgraphs, getIndex y' ntc)) )
             else (rev_completeComponentPath u)@[edge]
                  @(completeTermPath v y' (List.nth(sccSubgraphs, getIndex y' ntc)) )
           end
   in
      if x aconv y then
        [(Le (x, y, (Thm ([], #le_refl less_thms))))]
      else ( if xi = yi then completeTermPath x y (List.nth(sccSubgraphs, xi))
             else rev_completeComponentPath y )
   end;

(* ******************************************************************* *)
(* findLess e x y xi yi xreachable yreachable                          *)
(*                                                                     *)
(* Find a path from x through e to y, of weight <                      *)
(* ******************************************************************* *)

 fun findLess e x y xi yi xreachable yreachable =
  let val u = lower e
      val v = upper e
      val ui = getIndex u ntc
      val vi = getIndex v ntc

  in
      if ui mem xreachable andalso vi mem xreachable andalso
         ui mem yreachable andalso vi mem yreachable then (

  (case e of (Less (_, _, _)) =>
       let
        val (xufound, xupred) =  dfs (op =) sccGraph xi (getIndex u ntc)
            in
             if xufound then (
              let
               val (vyfound, vypred) =  dfs (op =) sccGraph (getIndex v ntc) yi
              in
               if vyfound then (
                let
                 val xypath = (completeComponentPath x u xupred)@[e]@(completeComponentPath v y vypred)
                 val xyLesss = transPath (tl xypath, hd xypath)
                in
                 if xyLesss subsumes subgoal then SOME (getprf xyLesss)
                 else NONE
               end)
               else NONE
              end)
             else NONE
            end
       |  _   =>
         let val (uvfound, uvpred) =  dfs (op =) sccGraph (getIndex u ntc) (getIndex v ntc)
             in
              if uvfound then (
               let
                val (xufound, xupred) = dfs (op =) sccGraph xi (getIndex u ntc)
               in
                if xufound then (
                 let
                  val (vyfound, vypred) =  dfs (op =) sccGraph (getIndex v ntc) yi
                 in
                  if vyfound then (
                   let
                    val uvpath = completeComponentPath u v uvpred
                    val uvLesss = mergeLess ( transPath (tl uvpath, hd uvpath), e)
                    val xypath = (completeComponentPath  x u xupred)@[uvLesss]@(completeComponentPath v y vypred)
                    val xyLesss = transPath (tl xypath, hd xypath)
                   in
                    if xyLesss subsumes subgoal then SOME (getprf xyLesss)
                    else NONE
                   end )
                  else NONE
                 end)
                else NONE
               end )
              else NONE
             end )
    ) else NONE
end;


in
  (* looking for x <= y: any path from x to y is sufficient *)
  case subgoal of (Le (x, y, _)) => (
  if null sccGraph then raise Cannot else (
   let
    val xi = getIndex x ntc
    val yi = getIndex y ntc
    (* searches in sccGraph a path from xi to yi *)
    val (found, pred) = dfs (op =) sccGraph xi yi
   in
    if found then (
       let val xypath = completeComponentPath x y pred
           val xyLesss = transPath (tl xypath, hd xypath)
       in
          (case xyLesss of
            (Less (_, _, q)) => if xyLesss subsumes subgoal then (Thm ([q], #less_imp_le less_thms))
                                else raise Cannot
             | _   => if xyLesss subsumes subgoal then (getprf xyLesss)
                      else raise Cannot)
       end )
     else raise Cannot
   end
    )
   )
 (* looking for x < y: particular path required, which is not necessarily
    found by normal dfs *)
 |   (Less (x, y, _)) => (
  if null sccGraph then raise Cannot else (
   let
    val xi = getIndex x ntc
    val yi = getIndex y ntc
    val sccGraph_transpose = transpose (op =) sccGraph
    (* all components that can be reached from component xi  *)
    val xreachable = dfs_int_reachable sccGraph xi
    (* all comonents reachable from y in the transposed graph sccGraph' *)
    val yreachable = dfs_int_reachable sccGraph_transpose yi
    (* for all edges u ~= v or u < v check if they are part of path x < y *)
    fun processNeqEdges [] = raise Cannot
    |   processNeqEdges (e::es) =
      case  (findLess e x y xi yi xreachable yreachable) of (SOME prf) => prf
      | _ => processNeqEdges es

    in
       processNeqEdges neqE
    end
  )
 )
| (NotEq (x, y, _)) => (
  (* if there aren't any edges that are candidate for a ~= raise Cannot *)
  if null neqE then raise Cannot
  (* if there aren't any edges that are candidate for <= then just search a edge in neqE that implies the subgoal *)
  else if null sccSubgraphs then (
     (case (Library.find_first (fn fact => fact subsumes subgoal) neqE, subgoal) of
       ( SOME (NotEq (x, y, p)), NotEq (x', y', _)) =>
          if  (x aconv x' andalso y aconv y') then p
          else Thm ([p], #not_sym less_thms)
     | ( SOME (Less (x, y, p)), NotEq (x', y', _)) =>
          if x aconv x' andalso y aconv y' then (Thm ([p], #less_imp_neq less_thms))
          else (Thm ([(Thm ([p], #less_imp_neq less_thms))], #not_sym less_thms))
     | _ => raise Cannot)
   ) else (

   let  val xi = getIndex x ntc
        val yi = getIndex y ntc
        val sccGraph_transpose = transpose (op =) sccGraph
        val xreachable = dfs_int_reachable sccGraph xi
        val yreachable = dfs_int_reachable sccGraph_transpose yi

        fun processNeqEdges [] = raise Cannot
        |   processNeqEdges (e::es) = (
            let val u = lower e
                val v = upper e
                val ui = getIndex u ntc
                val vi = getIndex v ntc

            in
                (* if x ~= y follows from edge e *)
                if e subsumes subgoal then (
                     case e of (Less (u, v, q)) => (
                       if u aconv x andalso v aconv y then (Thm ([q], #less_imp_neq less_thms))
                       else (Thm ([(Thm ([q], #less_imp_neq less_thms))], #not_sym less_thms))
                     )
                     |    (NotEq (u,v, q)) => (
                       if u aconv x andalso v aconv y then q
                       else (Thm ([q],  #not_sym less_thms))
                     )
                 )
                (* if SCC_x is linked to SCC_y via edge e *)
                 else if ui = xi andalso vi = yi then (
                   case e of (Less (_, _,_)) => (
                        let val xypath = (completeTermPath x u (List.nth(sccSubgraphs, ui)) ) @ [e] @ (completeTermPath v y (List.nth(sccSubgraphs, vi)) )
                            val xyLesss = transPath (tl xypath, hd xypath)
                        in  (Thm ([getprf xyLesss], #less_imp_neq less_thms)) end)
                   | _ => (
                        let
                            val xupath = completeTermPath x u  (List.nth(sccSubgraphs, ui))
                            val uxpath = completeTermPath u x  (List.nth(sccSubgraphs, ui))
                            val vypath = completeTermPath v y  (List.nth(sccSubgraphs, vi))
                            val yvpath = completeTermPath y v  (List.nth(sccSubgraphs, vi))
                            val xuLesss = transPath (tl xupath, hd xupath)
                            val uxLesss = transPath (tl uxpath, hd uxpath)
                            val vyLesss = transPath (tl vypath, hd vypath)
                            val yvLesss = transPath (tl yvpath, hd yvpath)
                            val x_eq_u =  (Thm ([(getprf xuLesss),(getprf uxLesss)], #eqI less_thms))
                            val v_eq_y =  (Thm ([(getprf vyLesss),(getprf yvLesss)], #eqI less_thms))
                        in
                           (Thm ([x_eq_u , (getprf e), v_eq_y ], #eq_neq_eq_imp_neq less_thms))
                        end
                        )
                  ) else if ui = yi andalso vi = xi then (
                     case e of (Less (_, _,_)) => (
                        let val xypath = (completeTermPath y u (List.nth(sccSubgraphs, ui)) ) @ [e] @ (completeTermPath v x (List.nth(sccSubgraphs, vi)) )
                            val xyLesss = transPath (tl xypath, hd xypath)
                        in (Thm ([(Thm ([getprf xyLesss], #less_imp_neq less_thms))] , #not_sym less_thms)) end )
                     | _ => (

                        let val yupath = completeTermPath y u (List.nth(sccSubgraphs, ui))
                            val uypath = completeTermPath u y (List.nth(sccSubgraphs, ui))
                            val vxpath = completeTermPath v x (List.nth(sccSubgraphs, vi))
                            val xvpath = completeTermPath x v (List.nth(sccSubgraphs, vi))
                            val yuLesss = transPath (tl yupath, hd yupath)
                            val uyLesss = transPath (tl uypath, hd uypath)
                            val vxLesss = transPath (tl vxpath, hd vxpath)
                            val xvLesss = transPath (tl xvpath, hd xvpath)
                            val y_eq_u =  (Thm ([(getprf yuLesss),(getprf uyLesss)], #eqI less_thms))
                            val v_eq_x =  (Thm ([(getprf vxLesss),(getprf xvLesss)], #eqI less_thms))
                        in
                            (Thm ([(Thm ([y_eq_u , (getprf e), v_eq_x ], #eq_neq_eq_imp_neq less_thms))], #not_sym less_thms))
                        end
                       )
                  ) else (
                       (* there exists a path x < y or y < x such that
                          x ~= y may be concluded *)
                        case  (findLess e x y xi yi xreachable yreachable) of
                              (SOME prf) =>  (Thm ([prf], #less_imp_neq less_thms))
                             | NONE =>  (
                               let
                                val yr = dfs_int_reachable sccGraph yi
                                val xr = dfs_int_reachable sccGraph_transpose xi
                               in
                                case  (findLess e y x yi xi yr xr) of
                                      (SOME prf) => (Thm ([(Thm ([prf], #less_imp_neq less_thms))], #not_sym less_thms))
                                      | _ => processNeqEdges es
                               end)
                 ) end)
     in processNeqEdges neqE end)
  )
end;


(* ******************************************************************* *)
(*                                                                     *)
(* mk_sccGraphs components leqG neqG ntc :                             *)
(* Term.term list list ->                                              *)
(* (Term.term * (Term.term * less) list) list ->                       *)
(* (Term.term * (Term.term * less) list) list ->                       *)
(* (Term.term * int)  list ->                                          *)
(* (int * (int * less) list) list   *                                  *)
(* ((Term.term * (Term.term * less) list) list) list                   *)
(*                                                                     *)
(*                                                                     *)
(* Computes, from graph leqG, list of all its components and the list  *)
(* ntc (nodes, index of component) a graph whose nodes are the         *)
(* indices of the components of g.  Egdes of the new graph are         *)
(* only the edges of g linking two components. Also computes for each  *)
(* component the subgraph of leqG that forms this component.           *)
(*                                                                     *)
(* For each component SCC_i is checked if there exists a edge in neqG  *)
(* that leads to a contradiction.                                      *)
(*                                                                     *)
(* We have a contradiction for edge u ~= v and u < v if:               *)
(* - u and v are in the same component,                                *)
(* that is, a path u <= v and a path v <= u exist, hence u = v.        *)
(* From irreflexivity of < follows u < u or v < v. Ex false quodlibet. *)
(*                                                                     *)
(* ******************************************************************* *)

fun mk_sccGraphs _ [] _ _ = ([],[])
|   mk_sccGraphs components leqG neqG ntc =
    let
    (* Liste (Index der Komponente, Komponente *)
    val IndexComp = indexComps components;


    fun handleContr edge g =
       (case edge of
          (Less  (x, y, _)) => (
            let
             val xxpath = edge :: (completeTermPath y x g )
             val xxLesss = transPath (tl xxpath, hd xxpath)
             val q = getprf xxLesss
            in
             raise (Contr (Thm ([q], #less_reflE less_thms )))
            end
          )
        | (NotEq (x, y, _)) => (
            let
             val xypath = (completeTermPath x y g )
             val yxpath = (completeTermPath y x g )
             val xyLesss = transPath (tl xypath, hd xypath)
             val yxLesss = transPath (tl yxpath, hd yxpath)
             val q = getprf (mergeLess ((mergeLess (edge, xyLesss)),yxLesss ))
            in
             raise (Contr (Thm ([q], #less_reflE less_thms )))
            end
         )
        | _ =>  error "trans_tac/handleContr: invalid Contradiction");


    (* k is index of the actual component *)

    fun processComponent (k, comp) =
     let
        (* all edges with weight <= of the actual component *)
        val leqEdges = List.concat (map (adjacent (op aconv) leqG) comp);
        (* all edges with weight ~= of the actual component *)
        val neqEdges = map snd (List.concat (map (adjacent (op aconv) neqG) comp));

       (* find an edge leading to a contradiction *)
       fun findContr [] = NONE
       |   findContr (e::es) =
                    let val ui = (getIndex (lower e) ntc)
                        val vi = (getIndex (upper e) ntc)
                    in
                        if ui = vi then  SOME e
                        else findContr es
                    end;

                (* sort edges into component internal edges and
                   edges pointing away from the component *)
                fun sortEdges  [] (intern,extern)  = (intern,extern)
                |   sortEdges  ((v,l)::es) (intern, extern) =
                    let val k' = getIndex v ntc in
                        if k' = k then
                            sortEdges es (l::intern, extern)
                        else sortEdges  es (intern, (k',l)::extern) end;

                (* Insert edge into sorted list of edges, where edge is
                    only added if
                    - it is found for the first time
                    - it is a <= edge and no parallel < edge was found earlier
                    - it is a < edge
                 *)
                 fun insert (h: int,l) [] = [(h,l)]
                 |   insert (h,l) ((k',l')::es) = if h = k' then (
                     case l of (Less (_, _, _)) => (h,l)::es
                     | _  => (case l' of (Less (_, _, _)) => (h,l')::es
                              | _ => (k',l)::es) )
                     else (k',l'):: insert (h,l) es;

                (* Reorganise list of edges such that
                    - duplicate edges are removed
                    - if a < edge and a <= edge exist at the same time,
                      remove <= edge *)
                 fun reOrganizeEdges [] sorted = sorted: (int * less) list
                 |   reOrganizeEdges (e::es) sorted = reOrganizeEdges es (insert e sorted);

                 (* construct the subgraph forming the strongly connected component
                    from the edge list *)
                 fun sccSubGraph [] g  = g
                 |   sccSubGraph (l::ls) g =
                          sccSubGraph ls (addEdge ((lower l),[((upper l),l)],g))

                 val (intern, extern) = sortEdges leqEdges ([], []);
                 val subGraph = sccSubGraph intern [];

     in
         case findContr neqEdges of SOME e => handleContr e subGraph
         | _ => ((k, (reOrganizeEdges (extern) [])), subGraph)
     end;

    val tmp =  map processComponent IndexComp
in
     ( (map fst tmp), (map snd tmp))
end;


(** Find proof if possible. **)

fun gen_solve mkconcl sign (asms, concl) =
 let
  val (leqG, neqG, neqE) = mkGraphs asms
  val components = scc_term leqG
  val ntc = indexNodes (indexComps components)
  val (sccGraph, sccSubgraphs) = mk_sccGraphs components leqG neqG ntc
 in
   let
   val (subgoals, prf) = mkconcl decomp less_thms sign concl
   fun solve facts less =
      (case triv_solv less of NONE => findProof (sccGraph, neqE, ntc, sccSubgraphs) less
      | SOME prf => prf )
  in
   map (solve asms) subgoals
  end
 end;

in
 SUBGOAL (fn (A, n) => fn st =>
  let
   val thy = ProofContext.theory_of ctxt;
   val rfrees = map Free (Term.rename_wrt_term A (Logic.strip_params A));
   val Hs = map prop_of prems @ map (fn H => subst_bounds (rfrees, H)) (Logic.strip_assums_hyp A)
   val C = subst_bounds (rfrees, Logic.strip_assums_concl A)
   val lesss = List.concat (ListPair.map (mkasm decomp less_thms thy) (Hs, 0 upto (length Hs - 1)))
   val prfs = gen_solve mkconcl thy (lesss, C);
   val (subgoals, prf) = mkconcl decomp less_thms thy C;
  in
   FOCUS (fn {prems = asms, ...} =>
     let val thms = map (prove (prems @ asms)) prfs
     in rtac (prove thms prf) 1 end) ctxt n st
  end
  handle Contr p =>
      (FOCUS (fn {prems = asms, ...} => rtac (prove asms p) 1) ctxt n st
        handle Subscript => Seq.empty)
   | Cannot => Seq.empty
   | Subscript => Seq.empty)
end;

(* partial_tac - solves partial orders *)
val partial_tac = gen_order_tac mkasm_partial mkconcl_partial;

(* linear_tac - solves linear/total orders *)
val linear_tac = gen_order_tac mkasm_linear mkconcl_linear;

end;
