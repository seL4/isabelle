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

types
  'a list

arities
  list :: (term) term


consts

  list      :: "'a item set => 'a item set"
  Rep_list  :: "'a list => 'a item"
  Abs_list  :: "'a item => 'a list"
  NIL       :: "'a item"
  CONS      :: "['a item, 'a item] => 'a item"
  Nil       :: "'a list"
  "#"       :: "['a, 'a list] => 'a list"                   	(infixr 65)
  List_case :: "['b, ['a item, 'a item]=>'b, 'a item] => 'b"
  List_rec  :: "['a item, 'b, ['a item, 'a item, 'b]=>'b] => 'b"
  list_case :: "['b, ['a, 'a list]=>'b, 'a list] => 'b"
  list_rec  :: "['a list, 'b, ['a, 'a list, 'b]=>'b] => 'b"
  Rep_map   :: "('b => 'a item) => ('b list => 'a item)"
  Abs_map   :: "('a item => 'b) => 'a item => 'b list"
  null      :: "'a list => bool"
  hd        :: "'a list => 'a"
  tl,ttl    :: "'a list => 'a list"
  mem		:: "['a, 'a list] => bool"			(infixl 55)
  list_all  :: "('a => bool) => ('a list => bool)"
  map       :: "('a=>'b) => ('a list => 'b list)"
  "@"	    :: "['a list, 'a list] => 'a list"			(infixr 65)
  filter    :: "['a => bool, 'a list] => 'a list"

  (* list Enumeration *)

  "[]"      :: "'a list"                            ("[]")
  "@list"   :: "args => 'a list"                    ("[(_)]")

  (* Special syntax for list_all and filter *)
  "@Alls"	:: "[idt, 'a list, bool] => bool"	("(2Alls _:_./ _)" 10)
  "@filter"	:: "[idt, 'a list, bool] => 'a list"	("(1[_:_ ./ _])")

translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"
  "[]"          == "Nil"

  "case xs of Nil => a | y#ys => b" == "list_case a (%y ys.b) xs"

  "[x:xs . P]"	== "filter (%x.P) xs"
  "Alls x:xs.P"	== "list_all (%x.P) xs"

defs
  (* Defining the Concrete Constructors *)
  NIL_def       "NIL == In0(Numb(0))"
  CONS_def      "CONS M N == In1(M $ N)"

inductive "list(A)"
  intrs
    NIL_I  "NIL: list(A)"
    CONS_I "[| a: A;  M: list(A) |] ==> CONS a M : list(A)"

rules
  (* Faking a Type Definition ... *)
  Rep_list          "Rep_list(xs): list(range(Leaf))"
  Rep_list_inverse  "Abs_list(Rep_list(xs)) = xs"
  Abs_list_inverse  "M: list(range(Leaf)) ==> Rep_list(Abs_list(M)) = M"


defs
  (* Defining the Abstract Constructors *)
  Nil_def       "Nil == Abs_list(NIL)"
  Cons_def      "x#xs == Abs_list(CONS (Leaf x) (Rep_list xs))"

  List_case_def "List_case c d == Case (%x.c) (Split d)"

  (* list Recursion -- the trancl is Essential; see list.ML *)

  List_rec_def
   "List_rec M c d == wfrec (trancl pred_sexp) M 
                           (List_case (%g.c) (%x y g. d x y (g y)))"

  list_rec_def
   "list_rec l c d == 
   List_rec (Rep_list l) c (%x y r. d (Inv Leaf x) (Abs_list y) r)"

  (* Generalized Map Functionals *)

  Rep_map_def "Rep_map f xs == list_rec xs NIL (%x l r. CONS (f x) r)"
  Abs_map_def "Abs_map g M == List_rec M Nil (%N L r. g(N)#r)"

  null_def      "null(xs)            == list_rec xs True (%x xs r.False)"
  hd_def        "hd(xs)              == list_rec xs (@x.True) (%x xs r.x)"
  tl_def        "tl(xs)              == list_rec xs (@xs.True) (%x xs r.xs)"
  (* a total version of tl: *)
  ttl_def	"ttl(xs)             == list_rec xs [] (%x xs r.xs)"

  mem_def	"x mem xs            == 
		   list_rec xs False (%y ys r. if y=x then True else r)"
  list_all_def  "list_all P xs       == list_rec xs True (%x l r. P(x) & r)"
  map_def       "map f xs            == list_rec xs [] (%x l r. f(x)#r)"
  append_def	"xs@ys               == list_rec xs ys (%x l r. x#r)"
  filter_def	"filter P xs         == 
                  list_rec xs [] (%x xs r. if P(x) then x#r else r)"

  list_case_def "list_case a f xs == list_rec xs a (%x xs r.f x xs)"

end
