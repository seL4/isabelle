(*  Title:      Integ.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

The integers as equivalence classes over nat*nat.
*)

Integ = Equiv + Arith +
constdefs
  intrel      :: "((nat * nat) * (nat * nat)) set"
  "intrel == {p. ? x1 y1 x2 y2. p=((x1::nat,y1),(x2,y2)) & x1+y2 = x2+y1}"

typedef (Integ)
  int = "{x::(nat*nat).True}/intrel"            (Equiv.quotient_def)

instance
  int :: {ord, plus, times, minus}

constdefs

  znat        :: nat => int                                  ("$# _" [80] 80)
  "$# m == Abs_Integ(intrel ^^ {(m,0)})"

  zminus      :: int => int                                  ("$~ _" [80] 80)
  "$~ Z == Abs_Integ(UN p:Rep_Integ(Z). split (%x y. intrel^^{(y,x)}) p)"

  znegative   :: int => bool
  "znegative(Z) == EX x y. x<y & (x,y::nat):Rep_Integ(Z)"

  zmagnitude  :: int => int
  "zmagnitude(Z) == Abs_Integ(UN p:Rep_Integ(Z).
                              split (%x y. intrel^^{((y-x) + (x-y),0)}) p)"

  zpred       :: int=>int
  "zpred(Z) == Z - $# Suc(0)"

  zsuc        :: int=>int
  "zsuc(Z) == Z + $# Suc(0)"

defs
  zadd_def
   "Z1 + Z2 == 
       Abs_Integ(UN p1:Rep_Integ(Z1). UN p2:Rep_Integ(Z2).   
           split (%x1 y1. split (%x2 y2. intrel^^{(x1+x2, y1+y2)}) p2) p1)"

  zdiff_def "Z1 - Z2 == Z1 + zminus(Z2)"

  zless_def "Z1<Z2 == znegative(Z1 - Z2)"

  zle_def   "Z1 <= (Z2::int) == ~(Z2 < Z1)"

  zmult_def
   "Z1 * Z2 == 
       Abs_Integ(UN p1:Rep_Integ(Z1). UN p2:Rep_Integ(Z2). split (%x1 y1.   
           split (%x2 y2. intrel^^{(x1*x2 + y1*y2, x1*y2 + y1*x2)}) p2) p1)"

end
