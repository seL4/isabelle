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

primrec
  "ins le x [] = [x]"
  "ins le x (y#ys) = (if le x y then (x#y#ys) else y#(ins le x ys))"
primrec
  "insort le [] = []"
  "insort le (x#xs) = ins le x (insort le xs)"
end

