(*  Title: 	Integ.thy
    ID:         $Id$
    Authors: 	Riccardo Mattolini, Dip. Sistemi e Informatica
        	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994 Universita' di Firenze
    Copyright   1993  University of Cambridge

The integers as equivalence classes over nat*nat.
*)

Integ = Equiv + Arith +
consts
  intrel      :: "((nat * nat) * (nat * nat)) set"

defs
  intrel_def
   "intrel == {p. ? x1 y1 x2 y2. p=((x1::nat,y1),(x2,y2)) & x1+y2 = x2+y1}"

subtype (Integ)
  int = "{x::(nat*nat).True}/intrel"		(Equiv.quotient_def)

instance
  int :: {ord, plus, times, minus}

consts
  zNat        :: "nat set"
  znat	      :: "nat => int"	   ("$# _" [80] 80)
  zminus      :: "int => int"	   ("$~ _" [80] 80)
  znegative   :: "int => bool"
  zmagnitude  :: "int => int"
  zdiv,zmod   :: "[int,int]=>int"  (infixl 70)
  zpred,zsuc  :: "int=>int"

defs
  zNat_def    "zNat == {x::nat. True}"

  znat_def    "$# m == Abs_Integ(intrel ^^ {(m,0)})"

  zminus_def
	"$~ Z == Abs_Integ(UN p:Rep_Integ(Z). split (%x y. intrel^^{(y,x)}) p)"

  znegative_def
      "znegative(Z) == EX x y. x<y & (x,y::nat):Rep_Integ(Z)"

  zmagnitude_def
      "zmagnitude(Z) == Abs_Integ(UN p:Rep_Integ(Z).split (%x y. intrel^^{((y-x) + (x-y),0)}) p)"

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

  zdiv_def
   "Z1 zdiv Z2 ==   
       Abs_Integ(UN p1:Rep_Integ(Z1). UN p2:Rep_Integ(Z2). split (%x1 y1.   
           split (%x2 y2. intrel^^{((x1-y1)div(x2-y2)+(y1-x1)div(y2-x2),   
           (x1-y1)div(y2-x2)+(y1-x1)div(x2-y2))}) p2) p1)"

  zmod_def
   "Z1 zmod Z2 ==   
       Abs_Integ(UN p1:Rep_Integ(Z1).UN p2:Rep_Integ(Z2).split (%x1 y1.   
           split (%x2 y2. intrel^^{((x1-y1)mod((x2-y2)+(y2-x2)),   
           (x1-y1)mod((x2-y2)+(x2-y2)))}) p2) p1)"

  zsuc_def     "zsuc(Z) == Z + $# Suc(0)"

  zpred_def    "zpred(Z) == Z - $# Suc(0)"
end
