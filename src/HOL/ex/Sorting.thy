(*  Title:      HOL/ex/sorting.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Specification of sorting
*)

Sorting = Main +
consts
  sorted1:: [['a,'a] => bool, 'a list] => bool
  sorted :: [['a,'a] => bool, 'a list] => bool
  multiset   :: 'a list => ('a => nat)

primrec
  "sorted1 le [] = True"
  "sorted1 le (x#xs) = ((case xs of [] => True | y#ys => le x y) &
                        sorted1 le xs)"

primrec
  "sorted le [] = True"
  "sorted le (x#xs) = ((!y:set xs. le x y) & sorted le xs)"

primrec
  "multiset [] y = 0"
  "multiset (x#xs) y = (if x=y then Suc(multiset xs y) else multiset xs y)"

constdefs
  total  :: (['a,'a] => bool) => bool
   "total r == (ALL x y. r x y | r y x)"
  
  transf :: (['a,'a] => bool) => bool
   "transf f == (ALL x y z. f x y & f y z --> f x z)"

end
