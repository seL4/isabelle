(*  Title:      HOL/NatDef.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Definition of types ind and nat.

Type nat is defined as a set Nat over type ind.
*)

NatDef = Wellfounded_Recursion +

(** type ind **)

global

types
  ind

arities
  ind :: term

consts
  Zero_Rep      :: ind
  Suc_Rep       :: ind => ind

rules
  (*the axiom of infinity in 2 parts*)
  inj_Suc_Rep           "inj(Suc_Rep)"
  Suc_Rep_not_Zero_Rep  "Suc_Rep(x) ~= Zero_Rep"



(** type nat **)

(* type definition *)

consts
  Nat' :: "ind set"

inductive Nat'
intrs
  Zero_RepI "Zero_Rep : Nat'"
  Suc_RepI  "i : Nat' ==> Suc_Rep i : Nat'"

typedef (Nat)
  nat = "Nat'"   (Nat'.Zero_RepI)

instance
  nat :: {ord, zero, one}


(* abstract constants and syntax *)

consts
  Suc       :: nat => nat
  pred_nat  :: "(nat * nat) set"

local

defs
  Zero_nat_def  "0 == Abs_Nat(Zero_Rep)"
  Suc_def       "Suc == (%n. Abs_Nat(Suc_Rep(Rep_Nat(n))))"
  One_nat_def	"1 == Suc 0"

  (*nat operations*)
  pred_nat_def  "pred_nat == {(m,n). n = Suc m}"

  less_def      "m<n == (m,n):trancl(pred_nat)"

  le_def        "m<=(n::nat) == ~(n<m)"

end
