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

rules

sorted1_Nil  "sorted1 f []"
sorted1_One  "sorted1 f [x]"
sorted1_Cons "sorted1 f (Cons x (y#zs)) = (f x y & sorted1 f (y#zs))"

sorted_Nil "sorted le []"
sorted_Cons "sorted le (x#xs) = ((Alls y:xs. le x y) & sorted le xs)"

mset_Nil "mset [] y = 0"
mset_Cons "mset (x#xs) y = (if x=y then Suc(mset xs y) else mset xs y)"

total_def  "total r == (!x y. r x y | r y x)"
transf_def "transf f == (!x y z. f x y & f y z --> f x z)"
end
