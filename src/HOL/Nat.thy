(*  Title:      HOL/Nat.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Definition of types ind and nat.

Type nat is defined as a set Nat over type ind.
*)

Nat = WF +

(** type ind **)

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
  nat :: ord


(* abstract constants and syntax *)

consts
  "0"       :: nat                ("0")
  Suc       :: nat => nat
  nat_case  :: ['a, nat => 'a, nat] => 'a
  pred_nat  :: "(nat * nat) set"
  nat_rec   :: ['a, [nat, 'a] => 'a, nat] => 'a

  Least     :: (nat=>bool) => nat    (binder "LEAST " 10)

syntax
  "1"       :: nat                ("1")
  "2"       :: nat                ("2")

translations
   "1"  == "Suc(0)"
   "2"  == "Suc(1)"
  "case p of 0 => a | Suc(y) => b" == "nat_case a (%y.b) p"

defs
  Zero_def      "0 == Abs_Nat(Zero_Rep)"
  Suc_def       "Suc == (%n. Abs_Nat(Suc_Rep(Rep_Nat(n))))"

  (*nat operations and recursion*)
  nat_case_def  "nat_case a f n == @z.  (n=0 --> z=a)  
                                        & (!x. n=Suc(x) --> z=f(x))"
  pred_nat_def  "pred_nat == {p. ? n. p = (n, Suc(n))}"

  less_def      "m<n == (m,n):trancl(pred_nat)"

  le_def        "m<=(n::nat) == ~(n<m)"

  nat_rec_def   "nat_rec c d ==
                 wfrec pred_nat (%f. nat_case c (%m. d m (f m)))"
  (*least number operator*)
  Least_def     "Least(P) == @k. P(k) & (ALL j. j<k --> ~P(j))"

(* start 8bit 1 *)
(* end 8bit 1 *)

end
