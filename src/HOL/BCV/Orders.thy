(*  Title:      HOL/BCV/Orders.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM

Orderings and some sets.
*)

Orders = Orders0 +

instance option :: (order)order (le_option_refl,le_option_trans,
                                 le_option_antisym,less_le_option)
instance list :: (order)order (le_list_refl,le_list_trans,
                               le_list_antisym,less_le_list)
instance "*" :: (order,order)order
                (le_prod_refl,le_prod_trans,le_prod_antisym,less_le_prod)

constdefs
 acc :: "'a::order set => bool"
"acc A == wf{(y,x) . x:A & y:A & x < y}"

 option :: 'a set => 'a option set
"option A == insert None {x . ? y:A. x = Some y}"

 listsn :: nat => 'a set => 'a list set
"listsn n A == {xs. length xs = n & set xs <= A}"

end
