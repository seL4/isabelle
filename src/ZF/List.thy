(*  Title:      ZF/List
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Lists in Zermelo-Fraenkel Set Theory 

map is a binding operator -- it applies to meta-level functions, not 
object-level functions.  This simplifies the final form of term_rec_conv,
although complicating its derivation.
*)

List = Datatype + Arith +

consts
  list       :: i=>i
  
datatype
  "list(A)" = Nil | Cons ("a:A", "l: list(A)")


syntax
 "[]"        :: i                                       ("[]")
 "@List"     :: is => i                                 ("[(_)]")

translations
  "[x, xs]"     == "Cons(x, [xs])"
  "[x]"         == "Cons(x, [])"
  "[]"          == "Nil"


consts
  length :: i=>i
  hd      :: i=>i
  tl      :: i=>i

primrec
  "length([]) = 0"
  "length(Cons(a,l)) = succ(length(l))"
  
primrec
  "hd(Cons(a,l)) = a"

primrec
  "tl([]) = []"
  "tl(Cons(a,l)) = l"


consts
  map        :: [i=>i, i] => i
  set_of_list :: i=>i
  "@"        :: [i,i]=>i                        (infixr 60)
  
primrec
  "map(f,[]) = []"
  "map(f,Cons(a,l)) = Cons(f(a), map(f,l))"
 
primrec
  "set_of_list([]) = 0"
  "set_of_list(Cons(a,l)) = cons(a, set_of_list(l))"
   
primrec
  "[] @ ys = ys"
  "(Cons(a,l)) @ ys = Cons(a, l @ ys)"
  

consts
  rev :: i=>i
  flat       :: i=>i
  list_add   :: i=>i

primrec
  "rev([]) = []"
  "rev(Cons(a,l)) = rev(l) @ [a]"

primrec
  "flat([]) = []"
  "flat(Cons(l,ls)) = l @ flat(ls)"
   
primrec
  "list_add([]) = 0"
  "list_add(Cons(a,l)) = a #+ list_add(l)"
       
consts
  drop       :: [i,i]=>i

primrec
  drop_0    "drop(0,l) = l"
  drop_SUCC "drop(succ(i), l) = tl (drop(i,l))"

end
