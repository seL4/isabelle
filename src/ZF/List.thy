(*  Title:      ZF/List
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Lists in Zermelo-Fraenkel Set Theory 

map is a binding operator -- it applies to meta-level functions, not 
object-level functions.  This simplifies the final form of term_rec_conv,
although complicating its derivation.
*)

List = Datatype + 

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


constdefs
  hd      :: i=>i
  "hd(l)       == list_case(0, %x xs.x, l)"
  
  tl      :: i=>i
  "tl(l)       == list_case(Nil, %x xs.xs, l)"
  
  drop       :: [i,i]=>i
  "drop(i,l)   == rec(i, l, %j r. tl(r))"

  list_rec   :: [i, i, [i,i,i]=>i] => i
  "list_rec(l,c,h) == Vrec(l, %l g.list_case(c, %x xs. h(x, xs, g`xs), l))"

  map        :: [i=>i, i] => i
  "map(f,l)    == list_rec(l,  Nil,  %x xs r. Cons(f(x), r))"

  length :: i=>i
  "length(l)   == list_rec(l,  0,  %x xs r. succ(r))"

  set_of_list :: i=>i
  "set_of_list(l)   == list_rec(l,  0,  %x xs r. cons(x,r))"

consts  (*Cannot use constdefs because @ is not an identifier*)
  "@"        :: [i,i]=>i                        (infixr 60)
defs
  app_def       "xs@ys       == list_rec(xs, ys, %x xs r. Cons(x,r))"


constdefs
  rev :: i=>i
  "rev(l)      == list_rec(l,  Nil,  %x xs r. r @ [x])"

  flat       :: i=>i
  "flat(ls)    == list_rec(ls, Nil,  %l ls r. l @ r)"

  list_add   :: i=>i
  "list_add(l) == list_rec(l, 0,  %x xs r. x#+r)"

end
