(*  Title:      ZF/ex/Bin.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Arithmetic on binary integers.

   The sign Pls stands for an infinite string of leading 0's.
   The sign Min stands for an infinite string of leading 1's.

A number can have multiple representations, namely leading 0's with sign
Pls and leading 1's with sign Min.  See twos-compl.ML/int_of_binary for
the numerical interpretation.

The representation expects that (m mod 2) is 0 or 1, even if m is negative;
For instance, ~5 div 2 = ~3 and ~5 mod 2 = 1; thus ~5 = (~3)*2 + 1

Division is not defined yet!
*)

Bin = Int + Datatype +

consts  bin :: i
datatype
  "bin" = Pls
        | Min
        | Bit ("w: bin", "b: bool")	(infixl "BIT" 90)

syntax
  "_Int"           :: xnum => i        ("_")

consts
  integ_of  :: i=>i
  NCons     :: [i,i]=>i
  bin_succ  :: i=>i
  bin_pred  :: i=>i
  bin_minus :: i=>i
  bin_add   :: [i,i]=>i
  bin_adder :: i=>i
  bin_mult  :: [i,i]=>i

primrec
  integ_of_Pls  "integ_of (Pls)     = $# 0"
  integ_of_Min  "integ_of (Min)     = $-($#1)"
  integ_of_BIT  "integ_of (w BIT b) = $#b $+ integ_of(w) $+ integ_of(w)"

    (** recall that cond(1,b,c)=b and cond(0,b,c)=0 **)

primrec (*NCons adds a bit, suppressing leading 0s and 1s*)
  NCons_Pls "NCons (Pls,b)     = cond(b,Pls BIT b,Pls)"
  NCons_Min "NCons (Min,b)     = cond(b,Min,Min BIT b)"
  NCons_BIT "NCons (w BIT c,b) = w BIT c BIT b"

primrec (*successor.  If a BIT, can change a 0 to a 1 without recursion.*)
  bin_succ_Pls  "bin_succ (Pls)     = Pls BIT 1"
  bin_succ_Min  "bin_succ (Min)     = Pls"
  bin_succ_BIT  "bin_succ (w BIT b) = cond(b, bin_succ(w) BIT 0, NCons(w,1))"

primrec (*predecessor*)
  bin_pred_Pls  "bin_pred (Pls)     = Min"
  bin_pred_Min  "bin_pred (Min)     = Min BIT 0"
  bin_pred_BIT  "bin_pred (w BIT b) = cond(b, NCons(w,0), bin_pred(w) BIT 1)"

primrec (*unary negation*)
  bin_minus_Pls
    "bin_minus (Pls)       = Pls"
  bin_minus_Min
    "bin_minus (Min)       = Pls BIT 1"
  bin_minus_BIT
    "bin_minus (w BIT b) = cond(b, bin_pred(NCons(bin_minus(w),0)),
				bin_minus(w) BIT 0)"

primrec (*sum*)
  bin_adder_Pls
    "bin_adder (Pls)     = (lam w:bin. w)"
  bin_adder_Min
    "bin_adder (Min)     = (lam w:bin. bin_pred(w))"
  bin_adder_BIT
    "bin_adder (v BIT x) = 
       (lam w:bin. 
         bin_case (v BIT x, bin_pred(v BIT x), 
                   %w y. NCons(bin_adder (v) ` cond(x and y, bin_succ(w), w),  
                               x xor y),
                   w))"

(*The bin_case above replaces the following mutually recursive function:
primrec
  "adding (v,x,Pls)     = v BIT x"
  "adding (v,x,Min)     = bin_pred(v BIT x)"
  "adding (v,x,w BIT y) = NCons(bin_adder (v, cond(x and y, bin_succ(w), w)), 
				x xor y)"
*)

defs
  bin_add_def "bin_add(v,w) == bin_adder(v)`w"


primrec
  bin_mult_Pls
    "bin_mult (Pls,w)     = Pls"
  bin_mult_Min
    "bin_mult (Min,w)     = bin_minus(w)"
  bin_mult_BIT
    "bin_mult (v BIT b,w) = cond(b, bin_add(NCons(bin_mult(v,w),0),w),
				 NCons(bin_mult(v,w),0))"

setup NumeralSyntax.setup

end


ML
