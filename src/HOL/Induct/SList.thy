(* *********************************************************************** *)
(*                                                                         *)
(* Title:      SList.thy (Extended List Theory)                            *)
(* Based on:   $Id$       *)
(* Author:     Lawrence C Paulson, Cambridge University Computer Laboratory*)
(* Author:     B. Wolff, University of Bremen                              *)
(* Purpose:    Enriched theory of lists                                    *)
(*	       mutual indirect recursive data-types                        *)
(*                                                                         *)
(* *********************************************************************** *)

(* Definition of type 'a list (strict lists) by a least fixed point

We use          list(A) == lfp(%Z. {NUMB(0)} <+> A <*> Z)
and not         list    == lfp(%Z. {NUMB(0)} <+> range(Leaf) <*> Z)

so that list can serve as a "functor" for defining other recursive types.

This enables the conservative construction of mutual recursive data-types
such as

datatype 'a m = Node 'a * ('a m) list

Tidied by lcp.  Still needs removal of nat_rec.
*)

SList = NatArith + Sexp + Hilbert_Choice (*gives us "inv"*) +
(* *********************************************************************** *)
(*                                                                         *)
(* Building up data type                                                   *)
(*                                                                         *)
(* *********************************************************************** *)

consts

  list      :: "'a item set => 'a item set"

  NIL       :: "'a item"
  CONS      :: "['a item, 'a item] => 'a item"
  List_case :: "['b, ['a item, 'a item]=>'b, 'a item] => 'b"
  List_rec  :: "['a item, 'b, ['a item, 'a item, 'b]=>'b] => 'b"

defs
  (* Defining the Concrete Constructors *)
  NIL_def           "NIL == In0(Numb(0))"
  CONS_def          "CONS M N == In1(Scons M N)"

inductive "list(A)"
  intrs
    NIL_I           "NIL: list A"
    CONS_I          "[| a: A;  M: list A |] ==> CONS a M : list A"


typedef (List)
  'a list = "list(range Leaf) :: 'a item set" (list.NIL_I)

defs
  List_case_def     "List_case c d == Case(%x. c)(Split(d))"
  
  List_rec_def
   "List_rec M c d == wfrec (trancl pred_sexp)
                            (%g. List_case c (%x y. d x y (g y))) M"


(* *********************************************************************** *)
(*                                                                         *)
(* Abstracting data type                                                   *)
(*                                                                         *)
(* *********************************************************************** *)

(*Declaring the abstract list constructors*)
consts
  Nil       :: "'a list"
  "#"       :: "['a, 'a list] => 'a list"           (infixr 65)
  list_case :: "['b, ['a, 'a list]=>'b, 'a list] => 'b"
  list_rec  :: "['a list, 'b, ['a, 'a list, 'b]=>'b] => 'b"


(* list Enumeration *)

  "[]"      :: "'a list"                            ("[]")
  "@list"   :: "args => 'a list"                    ("[(_)]")

translations
  "[x, xs]" == "x#[xs]"
  "[x]"     == "x#[]"
  "[]"      == "Nil"

  "case xs of Nil => a | y#ys => b" == "list_case(a, %y ys. b, xs)"



defs
  (* Defining the Abstract Constructors *)
  Nil_def           "Nil  == Abs_List(NIL)"
  Cons_def          "x#xs == Abs_List(CONS (Leaf x)(Rep_List xs))"

  list_case_def     "list_case a f xs == list_rec xs a (%x xs r. f x xs)"

  (* list Recursion -- the trancl is Essential; see list.ML *)

  list_rec_def
   "list_rec l c d ==                                              \
   \   List_rec(Rep_List l) c (%x y r. d(inv Leaf x)(Abs_List y) r)"


  
(* *********************************************************************** *)
(*                                                                         *)
(* Generalized Map Functionals                                             *)
(*                                                                         *)
(* *********************************************************************** *)

  
(* Generalized Map Functionals *)

consts
  Rep_map   :: "('b => 'a item) => ('b list => 'a item)"
  Abs_map   :: "('a item => 'b) => 'a item => 'b list"

defs
  Rep_map_def "Rep_map f xs == list_rec xs  NIL(%x l r. CONS(f x) r)"
  Abs_map_def "Abs_map g M  == List_rec M Nil (%N L r. g(N)#r)"


(**** Function definitions ****)

constdefs

  null      :: "'a list => bool"
  "null xs  == list_rec xs True (%x xs r. False)"

  hd        :: "'a list => 'a"
  "hd xs    == list_rec xs (@x. True) (%x xs r. x)"

  tl        :: "'a list => 'a list"
  "tl xs    == list_rec xs (@xs. True) (%x xs r. xs)"

  (* a total version of tl: *)
  ttl       :: "'a list => 'a list"
  "ttl xs   == list_rec xs [] (%x xs r. xs)"

  mem       :: "['a, 'a list] => bool"                              (infixl 55)
  "x mem xs == list_rec xs False (%y ys r. if y=x then True else r)"

  list_all  :: "('a => bool) => ('a list => bool)"
  "list_all P xs == list_rec xs True(%x l r. P(x) & r)"

  map       :: "('a=>'b) => ('a list => 'b list)"
  "map f xs == list_rec xs [] (%x l r. f(x)#r)"


consts
  "@"       :: ['a list, 'a list] => 'a list                        (infixr 65)
defs
  append_def"xs@ys == list_rec xs ys (%x l r. x#r)"


constdefs
  filter    :: "['a => bool, 'a list] => 'a list"
  "filter P xs == list_rec xs []  (%x xs r. if P(x)then x#r else r)"

  foldl     :: "[['b,'a] => 'b, 'b, 'a list] => 'b"
  "foldl f a xs == list_rec xs (%a. a)(%x xs r.%a. r(f a x))(a)"

  foldr     :: "[['a,'b] => 'b, 'b, 'a list] => 'b"
  "foldr f a xs     == list_rec xs a (%x xs r. (f x r))"

  length    :: "'a list => nat"
  "length xs== list_rec xs 0 (%x xs r. Suc r)"

  drop      :: "['a list,nat] => 'a list"
  "drop t n == (nat_rec(%x. x)(%m r xs. r(ttl xs)))(n)(t)"

  copy      :: "['a, nat] => 'a list"      (* make list of n copies of x *)
  "copy t   == nat_rec [] (%m xs. t # xs)"

  flat      :: "'a list list => 'a list"
  "flat     == foldr (op @) []"

  nth       :: "[nat, 'a list] => 'a"
  "nth      == nat_rec hd (%m r xs. r(tl xs))"

  rev       :: "'a list => 'a list"
  "rev xs   == list_rec xs [] (%x xs xsa. xsa @ [x])"


(* miscellaneous definitions *)
  zip       :: "'a list * 'b list => ('a*'b) list"
  "zip      == zipWith  (%s. s)"

  zipWith   :: "['a * 'b => 'c, 'a list * 'b list] => 'c list"
  "zipWith f S == (list_rec (fst S)  (%T.[])
                            (%x xs r. %T. if null T then [] 
                                          else f(x,hd T) # r(tl T)))(snd(S))"

  unzip     :: "('a*'b) list => ('a list * 'b list)"
  "unzip    == foldr(% (a,b)(c,d).(a#c,b#d))([],[])"


consts take      :: "['a list,nat] => 'a list"
primrec
  take_0  "take xs 0 = []"
  take_Suc "take xs (Suc n) = list_case [] (%x l. x # take l n) xs"

consts enum      :: "[nat,nat] => nat list"
primrec
  enum_0   "enum i 0 = []"
  enum_Suc "enum i (Suc j) = (if i <= j then enum i j @ [j] else [])"


syntax
  (* Special syntax for list_all and filter *)
  "@Alls"       :: "[idt, 'a list, bool] => bool"        ("(2Alls _:_./ _)" 10)
  "@filter"     :: "[idt, 'a list, bool] => 'a list"        ("(1[_:_ ./ _])")

translations
  "[x:xs. P]"   == "filter(%x. P) xs"
  "Alls x:xs. P"== "list_all(%x. P)xs"


end
