(*  Title:      HOL/BCV/Listn.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Lists of a fixed length
*)

Listn = Err +

constdefs

 list :: nat => 'a set => 'a list set
"list n A == {xs. length xs = n & set xs <= A}"

 le :: 'a ord => ('a list)ord
"le r == list_all2 (%x y. x <=_r y)"

syntax "@lesublist" :: 'a list => 'a ord => 'a list => bool
       ("(_ /<=[_] _)" [50, 0, 51] 50)
syntax "@lesssublist" :: 'a list => 'a ord => 'a list => bool
       ("(_ /<[_] _)" [50, 0, 51] 50)
translations
 "x <=[r] y" == "x <=_(Listn.le r) y"
 "x <[r] y"  == "x <_(Listn.le r) y"

constdefs
 map2 :: ('a => 'b => 'c) => 'a list => 'b list => 'c list
"map2 f == (%xs ys. map (split f) (zip xs ys))"

syntax "@plussublist" :: 'a list => ('a => 'b => 'c) => 'b list => 'c list
       ("(_ /+[_] _)" [65, 0, 66] 65)
translations  "x +[f] y" == "x +_(map2 f) y"

consts coalesce :: 'a err list => 'a list err
primrec
"coalesce [] = OK[]"
"coalesce (ex#exs) = Err.sup (op #) ex (coalesce exs)"

constdefs
 sl :: nat => 'a sl => 'a list sl
"sl n == %(A,r,f). (list n A, le r, map2 f)"

 sup :: ('a => 'b => 'c err) => 'a list => 'b list => 'c list err
"sup f == %xs ys. if size xs = size ys then coalesce(xs +[f] ys) else Err"

 upto_esl :: nat => 'a esl => 'a list esl
"upto_esl m == %(A,r,f). (Union{list n A |n. n <= m}, le r, sup f)"

end
