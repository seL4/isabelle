(*  Title:      HOL/Lambda/ListOrder.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen

Lifting an order to lists of elements, relating exactly one element
*)

ListOrder = Acc +

constdefs
 step1 :: "('a * 'a)set => ('a list * 'a list)set"
"step1 r ==
   {(ys,xs). ? us z z' vs. xs = us@z#vs & (z',z) : r & ys = us@z'#vs}"

end
