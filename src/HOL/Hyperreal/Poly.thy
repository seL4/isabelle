(*  Title:       Poly.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2000 University of Edinburgh
    Description: Properties of univariate real polynomials (cf. Harrison)
*)

Poly = Transcendental + 

(* ------------------------------------------------------------------------- *)
(* Application of polynomial as a real function.                             *)
(* ------------------------------------------------------------------------- *)

consts poly :: real list => real => real
primrec
  poly_Nil  "poly [] x = 0"
  poly_Cons "poly (h#t) x = h + x * poly t x"


(* ------------------------------------------------------------------------- *)
(* Arithmetic operations on polynomials.                                     *)
(* ------------------------------------------------------------------------- *)

(* addition *)
consts "+++" :: [real list, real list] => real list  (infixl 65)
primrec
  padd_Nil  "[] +++ l2 = l2"
  padd_Cons "(h#t) +++ l2 = (if l2 = [] then h#t 
                            else (h + hd l2)#(t +++ tl l2))"

(* Multiplication by a constant *)
consts "%*" :: [real, real list] => real list  (infixl 70)
primrec
   cmult_Nil  "c %* [] = []"
   cmult_Cons "c %* (h#t) = (c * h)#(c %* t)"

(* Multiplication by a polynomial *)
consts "***" :: [real list, real list] => real list  (infixl 70)
primrec
   pmult_Nil  "[] *** l2 = []"
   pmult_Cons "(h#t) *** l2 = (if t = [] then h %* l2 
                              else (h %* l2) +++ ((0) # (t *** l2)))"

(* Repeated multiplication by a polynomial *)
consts mulexp :: [nat, real list, real list] => real list
primrec
   mulexp_zero "mulexp 0 p q = q"
   mulexp_Suc  "mulexp (Suc n) p q = p *** mulexp n p q"
  
  
(* Exponential *)
consts "%^" :: [real list, nat] => real list  (infixl 80)
primrec
   pexp_0   "p %^ 0 = [1]"
   pexp_Suc "p %^ (Suc n) = p *** (p %^ n)"

(* Quotient related value of dividing a polynomial by x + a *)
(* Useful for divisor properties in inductive proofs *)
consts "pquot" :: [real list, real] => real list
primrec
   pquot_Nil  "pquot [] a= []"
   pquot_Cons "pquot (h#t) a = (if t = [] then [h]
                   else (inverse(a) * (h - hd( pquot t a)))#(pquot t a))"

(* ------------------------------------------------------------------------- *)
(* Differentiation of polynomials (needs an auxiliary function).             *)
(* ------------------------------------------------------------------------- *)
consts pderiv_aux :: nat => real list => real list
primrec
   pderiv_aux_Nil  "pderiv_aux n [] = []"
   pderiv_aux_Cons "pderiv_aux n (h#t) =
                     (real n * h)#(pderiv_aux (Suc n) t)"

(* ------------------------------------------------------------------------- *)
(* normalization of polynomials (remove extra 0 coeff)                       *)
(* ------------------------------------------------------------------------- *)
consts pnormalize :: real list => real list
primrec 
   pnormalize_Nil  "pnormalize [] = []"
   pnormalize_Cons "pnormalize (h#p) = (if ( (pnormalize p) = [])
                                     then (if (h = 0) then [] else [h]) 
                                     else (h#(pnormalize p)))"


(* ------------------------------------------------------------------------- *)
(* Other definitions                                                         *)
(* ------------------------------------------------------------------------- *)

constdefs
   poly_minus :: real list => real list      ("-- _" [80] 80)
   "-- p == (- 1) %* p"

   pderiv :: real list => real list
   "pderiv p == if p = [] then [] else pderiv_aux 1 (tl p)"

   divides :: [real list,real list] => bool (infixl 70)
   "p1 divides p2 == EX q. poly p2 = poly(p1 *** q)"

(* ------------------------------------------------------------------------- *)
(* Definition of order.                                                      *)
(* ------------------------------------------------------------------------- *)

   order :: real => real list => nat
   "order a p == (@n. ([-a, 1] %^ n) divides p &
                      ~ (([-a, 1] %^ (Suc n)) divides p))"

(* ------------------------------------------------------------------------- *)
(* Definition of degree.                                                     *)
(* ------------------------------------------------------------------------- *)

   degree :: real list => nat
   "degree p == length (pnormalize p)"
  
(* ------------------------------------------------------------------------- *)
(* Define being "squarefree" --- NB with respect to real roots only.         *)
(* ------------------------------------------------------------------------- *)

   rsquarefree :: real list => bool
   "rsquarefree p == poly p ~= poly [] &
                     (ALL a. (order a p = 0) | (order a p = 1))"

end
