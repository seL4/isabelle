(*  Title:      HOL/ex/Qsort.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Quicksort
*)

Qsort = Sorting +

(*Version one: higher-order*)
consts qsort :: "((['a,'a] => bool) * 'a list) => 'a list"

recdef qsort "measure (size o snd)"
    simpset "simpset() addsimps [length_filter RS le_less_trans]"
    
    "qsort(le, [])   = []"
    
    "qsort(le, x#xs) = qsort(le, [y:xs . ~ le x y])  
                       @ (x # qsort(le, [y:xs . le x y]))"


(*Version two: type classes*)
consts quickSort :: "('a::linorder) list => 'a list"

recdef quickSort "measure size"
    simpset "simpset() addsimps [length_filter RS le_less_trans]"
    
    "quickSort []   = []"
    
    "quickSort (x#l) = quickSort [y:l. ~ x<=y] @ (x # quickSort [y:l. x<=y])"

end
