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

typedef (Nat)
  nat = "lfp(%X. {Zero_Rep} Un (Suc_Rep``X))"   (lfp_def)

instance
  nat :: {ord, zero}


(* abstract constants and syntax *)

consts
  Suc       :: nat => nat
  pred_nat  :: "(nat * nat) set"

syntax
  "1"       :: nat                ("1")
  "2"       :: nat                ("2")

translations
  "1"  == "Suc 0"
  "2"  == "Suc 1"


local

defs
  Zero_def      "0 == Abs_Nat(Zero_Rep)"
  Suc_def       "Suc == (%n. Abs_Nat(Suc_Rep(Rep_Nat(n))))"

  (*nat operations*)
  pred_nat_def  "pred_nat == {(m,n). n = Suc m}"

  less_def      "m<n == (m,n):trancl(pred_nat)"

  le_def        "m<=(n::nat) == ~(n<m)"

end
