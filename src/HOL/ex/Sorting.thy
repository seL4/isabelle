(*  Title:      HOL/ex/sorting.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Specification of sorting
*)

Sorting = List +
consts
  sorted1:: [['a,'a] => bool, 'a list] => bool
  sorted :: [['a,'a] => bool, 'a list] => bool
  mset   :: 'a list => ('a => nat)
  total  :: (['a,'a] => bool) => bool
  transf :: (['a,'a] => bool) => bool

primrec sorted1 list
  "sorted1 le [] = True"
  "sorted1 le (x#xs) = ((case xs of [] => True | y#ys => le x y) &
                        sorted1 le xs)"

primrec sorted list
  "sorted le [] = True"
  "sorted le (x#xs) = ((!y:set_of_list xs. le x y) & sorted le xs)"

primrec mset list
  "mset [] y = 0"
  "mset (x#xs) y = (if x=y then Suc(mset xs y) else mset xs y)"

defs
total_def  "total r == (!x y. r x y | r y x)"
transf_def "transf f == (!x y z. f x y & f y z --> f x z)"
end
