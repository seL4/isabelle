(*  Title:      HOL/ex/SList.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Definition of type 'a list (strict lists) by a least fixed point

We use          list(A) == lfp(%Z. {NUMB(0)} <+> A <*> Z)
and not         list    == lfp(%Z. {NUMB(0)} <+> range(Leaf) <*> Z)
so that list can serve as a "functor" for defining other recursive types
*)

SList = Sexp +

consts

  list        :: 'a item set => 'a item set
  NIL         :: 'a item
  CONS        :: ['a item, 'a item] => 'a item
  List_case   :: ['b, ['a item, 'a item]=>'b, 'a item] => 'b
  List_rec    :: ['a item, 'b, ['a item, 'a item, 'b]=>'b] => 'b


defs
  (* Defining the Concrete Constructors *)
  NIL_def       "NIL == In0 (Numb 0)"
  CONS_def      "CONS M N == In1 (Scons M N)"

inductive "list(A)"
  intrs
    NIL_I  "NIL: list(A)"
    CONS_I "[| a: A;  M: list(A) |] ==> CONS a M : list(A)"


typedef (List)
  'a list = "list(range Leaf) :: 'a item set" (list.NIL_I)

  
(*Declaring the abstract list constructors*)
consts
  Nil         :: 'a list
  "#"         :: ['a, 'a list] => 'a list                         (infixr 65)

  (* list Enumeration *)

  "[]"        :: 'a list                              ("[]")
  "@list"     :: args => 'a list                      ("[(_)]")

  (* Special syntax for filter *)
  "@filter"   :: [idt, 'a list, bool] => 'a list      ("(1[_:_ ./ _])")


translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"
  "[]"          == "Nil"


defs
  Nil_def       "Nil  == Abs_List NIL"
  Cons_def      "x#xs == Abs_List(CONS (Leaf x) (Rep_List xs))"

  List_case_def "List_case c d == Case (%x. c) (Split d)"

  (* list Recursion -- the trancl is Essential; see list.ML *)

  List_rec_def
   "List_rec M c d == wfrec (trancl pred_sexp)
                            (%g. List_case c (%x y. d x y (g y))) M"




constdefs
  (* Generalized Map Functionals *)
  Rep_map     :: ('b => 'a item) => ('b list => 'a item)
    "Rep_map f xs == list_rec xs NIL (%x l r. CONS (f x) r)"
  
  Abs_map     :: ('a item => 'b) => 'a item => 'b list
    "Abs_map g M == List_rec M Nil (%N L r. g(N)#r)"


  list_rec    :: ['a list, 'b, ['a, 'a list, 'b]=>'b] => 'b
    "list_rec l c d == 
     List_rec (Rep_List l) c (%x y r. d (inv Leaf x) (Abs_List y) r)"

  null        :: 'a list => bool
    "null(xs)            == list_rec xs True (%x xs r. False)"

  hd          :: 'a list => 'a
    "hd(xs)              == list_rec xs arbitrary (%x xs r. x)"

  tl          :: 'a list => 'a list
     "tl(xs)              == list_rec xs arbitrary (%x xs r. xs)"

  (* a total version of tl *)
  ttl         :: 'a list => 'a list
    "ttl(xs)             == list_rec xs [] (%x xs r. xs)"

  set         :: ('a list => 'a set)
    "set xs              == list_rec xs {} (%x l r. insert x r)"

  mem         :: ['a, 'a list] => bool                            (infixl 55)
    "x mem xs == list_rec xs False (%y ys r. if y=x then True else r)"

  map         :: ('a=>'b) => ('a list => 'b list)
    "map f xs            == list_rec xs [] (%x l r. f(x)#r)"

  filter      :: ['a => bool, 'a list] => 'a list
    "filter P xs == list_rec xs [] (%x xs r. if P(x) then x#r else r)"

  list_case   :: ['b, ['a, 'a list]=>'b, 'a list] => 'b
    "list_case a f xs == list_rec xs a (%x xs r. f x xs)"


consts
  "@" :: ['a list, 'a list] => 'a list                    (infixr 65)

defs
  append_def  "xs@ys == list_rec xs ys (%x l r. x#r)"


translations
  "case xs of Nil => a | y#ys => b" == "list_case a (%y ys. b) xs"

  "[x:xs . P]"  == "filter (%x. P) xs"

end
