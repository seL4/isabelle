(*  Title:      HOL/Induct/ABexp.thy
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    Copyright   1998  TU Muenchen

Arithmetic and boolean expressions
*)

ABexp = Main +

datatype
  'a aexp = If_then_else ('a bexp) ('a aexp) ('a aexp)
          | Sum ('a aexp) ('a aexp)
          | Diff ('a aexp) ('a aexp)
          | Var 'a
          | Num nat
and
  'a bexp = Less ('a aexp) ('a aexp)
          | And ('a bexp) ('a bexp)
          | Or ('a bexp) ('a bexp)


(** evaluation of arithmetic and boolean expressions **)

consts
  eval_aexp :: "['a => nat, 'a aexp] => nat"
  eval_bexp :: "['a => nat, 'a bexp] => bool"

primrec
  "eval_aexp env (If_then_else b a1 a2) =
     (if eval_bexp env b then eval_aexp env a1 else eval_aexp env a2)"
  "eval_aexp env (Sum a1 a2) = eval_aexp env a1 + eval_aexp env a2"
  "eval_aexp env (Diff a1 a2) = eval_aexp env a1 - eval_aexp env a2"
  "eval_aexp env (Var v) = env v"
  "eval_aexp env (Num n) = n"

  "eval_bexp env (Less a1 a2) = (eval_aexp env a1 < eval_aexp env a2)"
  "eval_bexp env (And b1 b2) = (eval_bexp env b1 & eval_bexp env b2)"
  "eval_bexp env (Or b1 b2) = (eval_bexp env b1 & eval_bexp env b2)"


(** substitution on arithmetic and boolean expressions **)

consts
  subst_aexp :: "['a => 'b aexp, 'a aexp] => 'b aexp"
  subst_bexp :: "['a => 'b aexp, 'a bexp] => 'b bexp"

primrec
  "subst_aexp f (If_then_else b a1 a2) =
     If_then_else (subst_bexp f b) (subst_aexp f a1) (subst_aexp f a2)"
  "subst_aexp f (Sum a1 a2) = Sum (subst_aexp f a1) (subst_aexp f a2)"
  "subst_aexp f (Diff a1 a2) = Diff (subst_aexp f a1) (subst_aexp f a2)"
  "subst_aexp f (Var v) = f v"
  "subst_aexp f (Num n) = Num n"

  "subst_bexp f (Less a1 a2) = Less (subst_aexp f a1) (subst_aexp f a2)"
  "subst_bexp f (And b1 b2) = And (subst_bexp f b1) (subst_bexp f b2)"
  "subst_bexp f (Or b1 b2) = Or (subst_bexp f b1) (subst_bexp f b2)"

end
