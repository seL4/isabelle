(*  Title:      ZF/IntDiv.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

The division operators div, mod
*)

IntDiv = IntArith + OrderArith + 

constdefs
  quorem :: "[i,i] => o"
    "quorem == %<a,b> <q,r>.
                      a = b$*q $+ r &
                      (#0$<b & #0$<=r & r$<b | ~(#0$<b) & b$<r & r $<= #0)"

  adjust :: "[i,i,i] => i"
    "adjust(a,b) == %<q,r>. if #0 $<= r$-b then <#2$*q $+ #1,r$-b>
                            else <#2$*q,r>"


(** the division algorithm **)

constdefs posDivAlg :: "i => i"
(*for the case a>=0, b>0*)
(*recdef posDivAlg "inv_image less_than (%(a,b). nat_of(a $- b $+ #1))"*)
    "posDivAlg(ab) ==
       wfrec(measure(int*int, %<a,b>. nat_of (a $- b $+ #1)),
	     ab,
	     %<a,b> f. if (a$<b | b$<=#0) then <#0,a>
                       else adjust(a, b, f ` <a,#2$*b>))"


(*for the case a<0, b>0*)
constdefs negDivAlg :: "i => i"
(*recdef negDivAlg "inv_image less_than (%(a,b). nat_of(- a $- b))"*)
    "negDivAlg(ab) ==
       wfrec(measure(int*int, %<a,b>. nat_of ($- a $- b)),
	     ab,
	     %<a,b> f. if (#0 $<= a$+b | b$<=#0) then <#-1,a$+b>
                       else adjust(a, b, f ` <a,#2$*b>))"

(*for the general case b\\<noteq>0*)

constdefs
  negateSnd :: "i => i"
    "negateSnd == %<q,r>. <q, $-r>"

  (*The full division algorithm considers all possible signs for a, b
    including the special case a=0, b<0, because negDivAlg requires a<0*)
  divAlg :: "i => i"
    "divAlg ==
       %<a,b>. if #0 $<= a then
                  if #0 $<= b then posDivAlg (<a,b>)
                  else if a=#0 then <#0,#0>
                       else negateSnd (negDivAlg (<$-a,$-b>))
               else 
                  if #0$<b then negDivAlg (<a,b>)
                  else         negateSnd (posDivAlg (<$-a,$-b>))"

  zdiv  :: [i,i]=>i                    (infixl "zdiv" 70) 
    "a zdiv b == fst (divAlg (<intify(a), intify(b)>))"

  zmod  :: [i,i]=>i                    (infixl "zmod" 70)
    "a zmod b == snd (divAlg (<intify(a), intify(b)>))"

end
