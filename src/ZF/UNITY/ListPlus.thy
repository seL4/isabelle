(*  Title:      ZF/UNITY/ListPlus.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

More about lists

*)

ListPlus = NatPlus + 

constdefs
(* Function `take' returns the first n elements of a list *)
  take     :: [i,i]=>i
  "take(n, as) == list_rec(lam n:nat. [],
		%a l r. lam n:nat. nat_case([], %m. Cons(a, r`m), n), as)`n"
  
(* Function `nth' returns the (n+1)th element in a list (not defined at Nil) *)
  
  nth :: [i, i]=>i
  "nth(n, as) == list_rec(lam n:nat. 0,
		%a l r. lam n:nat. nat_case(a, %m. r`m, n), as)`n"

end