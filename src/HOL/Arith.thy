(*  Title:      HOL/Arith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Arithmetic operators and their definitions
*)

Arith = Nat +

instance
  nat :: {plus, minus, times}

consts
  pred      :: "nat => nat"
  div, mod  :: "[nat, nat] => nat"  (infixl 70)

defs
  pred_def  "pred(m) == nat_rec m 0 (%n r.n)"
  add_def   "m+n == nat_rec m n (%u v. Suc(v))"
  diff_def  "m-n == nat_rec n m (%u v. pred(v))"
  mult_def  "m*n == nat_rec m 0 (%u v. n + v)"
  mod_def   "m mod n == wfrec (trancl pred_nat) m (%j f.(if (j<n) j (f (j-n))))"
  div_def   "m div n == wfrec (trancl pred_nat) m (%j f.(if (j<n) 0 (Suc (f (j-n)))))"
end

(*"Difference" is subtraction of natural numbers.
  There are no negative numbers; we have
     m - n = 0  iff  m<=n   and     m - n = Suc(k) iff m>n.
  Also, nat_rec(m, 0, %z w.z) is pred(m).   *)

