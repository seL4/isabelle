(*  Title: 	ZF/List
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Lists in Zermelo-Fraenkel Set Theory 

map is a binding operator -- it applies to meta-level functions, not 
object-level functions.  This simplifies the final form of term_rec_conv,
although complicating its derivation.
*)

List = "Datatype" + Univ + 

consts
  "@"	     :: "[i,i]=>i"      			(infixr 60)
  list_rec   :: "[i, i, [i,i,i]=>i] => i"
  map 	     :: "[i=>i, i] => i"
  length,rev :: "i=>i"
  flat       :: "i=>i"
  list_add   :: "i=>i"
  hd,tl      :: "i=>i"
  drop	     :: "[i,i]=>i"

 (* List Enumeration *)
 "[]"        :: "i" 	                           	("[]")
 "@List"     :: "is => i" 	                   	("[(_)]")

  list	     :: "i=>i"

  
datatype
  "list(A)" = "Nil" | "Cons" ("a:A", "l: list(A)")


translations
  "[x, xs]"     == "Cons(x, [xs])"
  "[x]"         == "Cons(x, [])"
  "[]"          == "Nil"


rules

  hd_def	"hd(l)	     == list_case(0, %x xs.x, l)"
  tl_def	"tl(l)       == list_case(Nil, %x xs.xs, l)"
  drop_def	"drop(i,l)   == rec(i, l, %j r. tl(r))"

  list_rec_def
      "list_rec(l,c,h) == Vrec(l, %l g.list_case(c, %x xs. h(x, xs, g`xs), l))"

  map_def       "map(f,l)    == list_rec(l,  Nil,  %x xs r. Cons(f(x), r))"
  length_def    "length(l)   == list_rec(l,  0,  %x xs r. succ(r))"
  app_def       "xs@ys       == list_rec(xs, ys, %x xs r. Cons(x,r))"
  rev_def       "rev(l)      == list_rec(l,  Nil,  %x xs r. r @ [x])"
  flat_def      "flat(ls)    == list_rec(ls, Nil,  %l ls r. l @ r)"
  list_add_def  "list_add(l) == list_rec(l, 0,  %x xs r. x#+r)"
end
