(*  Title: 	HOL/ex/qsort.thy
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1994 TU Muenchen

Quicksort
*)

Qsort = Sorting +
consts
  qsort  :: [['a,'a] => bool, 'a list] => 'a list

rules

qsort_Nil  "qsort le [] = []"
qsort_Cons "qsort le (x#xs) = qsort le [y:xs . ~le x y] @ 
                            (x# qsort le [y:xs . le x y])"

(* computational induction.
   The dependence of p on x but not xs is intentional.
*)
qsort_ind
 "[| P([]); 
    !!x xs. [| P([y:xs . ~p x y]); P([y:xs . p x y]) |] ==> 
            P(x#xs) |] 
 ==> P(xs)"
end
