(*  Title:      HOL/IntDiv.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

The division operators div, mod and the divides relation "dvd"
*)

IntDiv = IntArith + Recdef + 

constdefs
  quorem :: "(int*int) * (int*int) => bool"
    "quorem == %((a,b), (q,r)).
                      a = b*q + r &
                      (if #0<b then #0<=r & r<b else b<r & r <= #0)"

  adjust :: "[int, int, int*int] => int*int"
    "adjust a b == %(q,r). if #0 <= r-b then (#2*q + #1, r-b)
                           else (#2*q, r)"

(** the division algorithm **)

(*for the case a>=0, b>0*)
consts posDivAlg :: "int*int => int*int"
recdef posDivAlg "inv_image less_than (%(a,b). nat(a - b + #1))"
    "posDivAlg (a,b) =
       (if (a<b | b<=#0) then (#0,a)
        else adjust a b (posDivAlg(a, #2*b)))"

(*for the case a<0, b>0*)
consts negDivAlg :: "int*int => int*int"
recdef negDivAlg "inv_image less_than (%(a,b). nat(- a - b))"
    "negDivAlg (a,b) =
       (if (#0<=a+b | b<=#0) then (#-1,a+b)
        else adjust a b (negDivAlg(a, #2*b)))"

(*for the general case b~=0*)

constdefs
  negateSnd :: "int*int => int*int"
    "negateSnd == %(q,r). (q,-r)"

  (*The full division algorithm considers all possible signs for a, b
    including the special case a=0, b<0, because negDivAlg requires a<0*)
  divAlg :: "int*int => int*int"
    "divAlg ==
       %(a,b). if #0<=a then
                  if #0<=b then posDivAlg (a,b)
                  else if a=#0 then (#0,#0)
                       else negateSnd (negDivAlg (-a,-b))
               else 
                  if #0<b then negDivAlg (a,b)
                  else         negateSnd (posDivAlg (-a,-b))"

instance
  int :: "Divides.div"        (*avoid clash with 'div' token*)

defs
  div_def   "a div b == fst (divAlg (a,b))"
  mod_def   "a mod b == snd (divAlg (a,b))"


end
