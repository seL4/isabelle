(*  Title:      HOL/ex/Qsort.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Quicksort
*)

Qsort = Sorting +
consts qsort :: "((['a,'a] => bool) * 'a list) => 'a list"

recdef qsort "measure (size o snd)"
    simpset "simpset() addsimps [less_Suc_eq_le]"
    
    "qsort(le, [])   = []"
    
    "qsort(le, x#xs) = qsort(le, [y:xs . ~ le x y])  
                       @ (x # qsort(le, [y:xs . le x y]))"

end
