(*  Title:      HOL/BCV/Product.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Products as semilattices
*)

Product = Err +

constdefs
 le :: "'a ord => 'b ord => ('a * 'b) ord"
"le rA rB == %(a,b) (a',b'). a <=_rA a' & b <=_rB b'"

 sup :: "'a ebinop => 'b ebinop => ('a * 'b)ebinop"
"sup f g == %(a1,b1)(a2,b2). Err.sup Pair (a1 +_f a2) (b1 +_g b2)"

 esl :: "'a esl => 'b esl => ('a * 'b ) esl"
"esl == %(A,rA,fA) (B,rB,fB). (A <*> B, le rA rB, sup fA fB)"

syntax "@lesubprod" :: "'a*'b => 'a ord => 'b ord => 'b => bool"
       ("(_ /<='(_,_') _)" [50, 0, 0, 51] 50)
translations "p <=(rA,rB) q" == "p <=_(Product.le rA rB) q"

end
