(*  Title       : Zorn.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Zorn's Lemma -- See lcp's Zorn.thy in ZF
*) 

Zorn = Main +  

constdefs
  chain     ::  'a set => 'a set set
    "chain S  == {F. F <= S & (ALL x: F. ALL y: F. x <= y | y <= x)}" 

  super     ::  ['a set,'a set] => (('a set) set) 
    "super S c == {d. d: chain(S) & c < d}"

  maxchain  ::  'a set => 'a set set
    "maxchain S == {c. c: chain S & super S c = {}}"

  succ      ::  ['a set,'a set] => 'a set
    "succ S c == if (c ~: chain S| c: maxchain S) 
                 then c else (@c'. c': (super S c))" 

consts 
  "TFin" :: 'a set => 'a set set

inductive "TFin(S)"
  intrs
    succI        "x : TFin S ==> succ S x : TFin S"
    Pow_UnionI   "Y : Pow(TFin S) ==> Union(Y) : TFin S"
           
  monos          Pow_mono
end

