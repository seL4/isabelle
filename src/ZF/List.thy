(*  Title:      ZF/List
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Lists in Zermelo-Fraenkel Set Theory 

map is a binding operator -- it applies to meta-level functions, not 
object-level functions.  This simplifies the final form of term_rec_conv,
although complicating its derivation.
*)

List = Datatype + ArithSimp +

consts
  list       :: "i=>i"
  
datatype
  "list(A)" = Nil | Cons ("a:A", "l: list(A)")


syntax
 "[]"        :: i                                       ("[]")
 "@List"     :: "is => i"                                 ("[(_)]")

translations
  "[x, xs]"     == "Cons(x, [xs])"
  "[x]"         == "Cons(x, [])"
  "[]"          == "Nil"


consts
  length :: "i=>i"
  hd      :: "i=>i"
  tl      :: "i=>i"

primrec
  "length([]) = 0"
  "length(Cons(a,l)) = succ(length(l))"
  
primrec
  "hd(Cons(a,l)) = a"

primrec
  "tl([]) = []"
  "tl(Cons(a,l)) = l"


consts
  map        :: "[i=>i, i] => i"
  set_of_list :: "i=>i"
  "@"        :: "[i,i]=>i"                        (infixr 60)
  
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
  rev :: "i=>i"
  flat       :: "i=>i"
  list_add   :: "i=>i"

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
  drop       :: "[i,i]=>i"

primrec
  drop_0    "drop(0,l) = l"
  drop_SUCC "drop(succ(i), l) = tl (drop(i,l))"


(*** Thanks to Sidi Ehmety for the following ***)

constdefs
(* Function `take' returns the first n elements of a list *)
  take     :: "[i,i]=>i"
  "take(n, as) == list_rec(lam n:nat. [],
		%a l r. lam n:nat. nat_case([], %m. Cons(a, r`m), n), as)`n"
  
(* Function `nth' returns the (n+1)th element in a list (not defined at Nil) *)
  nth :: "[i, i]=>i"
  "nth(n, as) == list_rec(lam n:nat. 0,
		%a l r. lam n:nat. nat_case(a, %m. r`m, n), as)`n"

  list_update :: "[i, i, i]=>i"
  "list_update(xs, i, v) == list_rec(lam n:nat. Nil,
      %u us vs. lam n:nat. nat_case(Cons(v, us), %m. Cons(u, vs`m), n), xs)`i"

consts
  filter :: "[i=>o, i] => i"
  zip :: "[i, i]=>i"
  ziprel :: "[i,i]=>i"
  upt :: "[i, i] =>i"
  
inductive domains "ziprel(A, B)" <= "list(A)*list(B)*list(A*B)"
intrs   
  ziprel_Nil1  "ys:list(B) ==><Nil, ys, Nil>:ziprel(A, B)"
  ziprel_Nil2  "xs:list(A) ==><xs, Nil, Nil>:ziprel(A, B)"
  ziprel_Cons "[| <xs, ys, zs>:ziprel(A, B); x:A; y:B |]==>
	         <Cons(x, xs), Cons(y, ys), Cons(<x, y>, zs)>:ziprel(A,B)"
  type_intrs  "list.intrs"
  
defs
  zip_def "zip(xs, ys) ==
	      THE zs. <xs, ys, zs>:ziprel(set_of_list(xs),set_of_list(ys))"

primrec
  "filter(P, Nil) = Nil"
  "filter(P, Cons(x, xs)) =
     (if P(x) then Cons(x, filter(P, xs)) else filter(P, xs))"

primrec
  "upt(i, 0) = Nil"
  "upt(i, succ(j)) = (if i le j then upt(i, j)@[j] else Nil)"

constdefs
  sublist :: "[i, i] => i"
    "sublist(xs, A)== 
     map(fst, (filter(%p. snd(p): A, zip(xs, upt(0,length(xs))))))"

  min :: "[i,i] =>i"
    "min(x, y) == (if x le y then x else y)"
  
  max :: "[i, i] =>i"
    "max(x, y) == (if x le y then y else x)"

end
