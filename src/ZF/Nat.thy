(*  Title:      ZF/Nat.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Natural numbers in Zermelo-Fraenkel Set Theory 
*)

Nat = OrdQuant + Bool + mono +

constdefs
  nat :: i
    "nat == lfp(Inf, %X. {0} Un {succ(i). i:X})"

  nat_case :: "[i, i=>i, i]=>i"
    "nat_case(a,b,k) == THE y. k=0 & y=a | (EX x. k=succ(x) & y=b(x))"

  nat_rec :: "[i, i, [i,i]=>i]=>i"
    "nat_rec(k,a,b) ==   
          wfrec(Memrel(nat), k, %n f. nat_case(a, %m. b(m, f`m), n))"

  (*Internalized relations on the naturals*)
  
  Le :: i
    "Le == {<x,y>:nat*nat. x le y}"

  Lt :: i
    "Lt == {<x, y>:nat*nat. x < y}"
  
  Ge :: i
    "Ge == {<x,y>:nat*nat. y le x}"

  Gt :: i
    "Gt == {<x,y>:nat*nat. y < x}"

  less_than :: i=>i
    "less_than(n) == {i:nat.  i<n}"

  greater_than :: i=>i
    "greater_than(n) == {i:nat. n < i}"

end
