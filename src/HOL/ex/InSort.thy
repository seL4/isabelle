(*  Title:      HOL/ex/insort.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Insertion sort
*)

InSort  =  Sorting +

consts
  ins :: [['a,'a]=>bool, 'a, 'a list] => 'a list
  insort :: [['a,'a]=>bool, 'a list] => 'a list

primrec ins List.list
  "ins f x [] = [x]"
  "ins f x (y#ys) = (if f x y then (x#y#ys) else y#(ins f x ys))"
primrec insort List.list
  "insort f [] = []"
  "insort f (x#xs) = ins f x (insort f xs)"
end

