(*  Title:      IntDef.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

The integers as equivalence classes over nat*nat.
*)

IntDef = Equiv + Arith +
constdefs
  intrel      :: "((nat * nat) * (nat * nat)) set"
  "intrel == {p. ? x1 y1 x2 y2. p=((x1::nat,y1),(x2,y2)) & x1+y2 = x2+y1}"

typedef (Integ)
  int = "{x::(nat*nat).True}/intrel"            (Equiv.quotient_def)

instance
  int :: {ord, plus, times, minus}

defs
  zminus_def
    "- Z == Abs_Integ(UN p:Rep_Integ(Z). split (%x y. intrel^^{(y,x)}) p)"

constdefs

  int :: nat => int
  "int m == Abs_Integ(intrel ^^ {(m,0)})"

  neg   :: int => bool
  "neg(Z) == EX x y. x<y & (x,y::nat):Rep_Integ(Z)"

  (*For simplifying equalities*)
  iszero :: int => bool
  "iszero z == z = int 0"
  
defs
  zadd_def
   "z + w == 
       Abs_Integ(UN p1:Rep_Integ(z). UN p2:Rep_Integ(w).   
           split (%x1 y1. split (%x2 y2. intrel^^{(x1+x2, y1+y2)}) p2) p1)"

  zdiff_def "z - (w::int) == z + (-w)"

  zless_def "z<w == neg(z - w)"

  zle_def   "z <= (w::int) == ~(w < z)"

  zmult_def
   "z * w == 
       Abs_Integ(UN p1:Rep_Integ(z). UN p2:Rep_Integ(w). split (%x1 y1.   
           split (%x2 y2. intrel^^{(x1*x2 + y1*y2, x1*y2 + y1*x2)}) p2) p1)"

end
