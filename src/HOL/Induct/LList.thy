(*  Title:      HOL/LList.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Definition of type 'a llist by a greatest fixed point

Shares NIL, CONS, List_case with List.thy

Still needs filter and flatten functions -- hard because they need
bounds on the amount of lookahead required.

Could try (but would it work for the gfp analogue of term?)
  LListD_Fun_def "LListD_Fun(A) == (%Z. diag({Numb(0)}) <++> diag(A) <**> Z)"

A nice but complex example would be [ML for the Working Programmer, page 176]
  from(1) = enumerate (Lmap (Lmap(pack), makeqq(from(1),from(1))))

Previous definition of llistD_Fun was explicit:
  llistD_Fun_def
   "llistD_Fun(r) ==    
       {(LNil,LNil)}  Un        
       (UN x. (split(%l1 l2.(LCons(x,l1),LCons(x,l2))))``r)"
*)

LList = Gfp + SList +

types
  'a llist

arities
   llist :: (term)term

consts
  list_Fun   :: ['a item set, 'a item set] => 'a item set
  LListD_Fun :: 
      "[('a item * 'a item)set, ('a item * 'a item)set] => 
      ('a item * 'a item)set"

  llist      :: 'a item set => 'a item set
  LListD     :: "('a item * 'a item)set => ('a item * 'a item)set"
  llistD_Fun :: "('a llist * 'a llist)set => ('a llist * 'a llist)set"

  Rep_llist  :: 'a llist => 'a item
  Abs_llist  :: 'a item => 'a llist
  LNil       :: 'a llist
  LCons      :: ['a, 'a llist] => 'a llist
  
  llist_case :: ['b, ['a, 'a llist]=>'b, 'a llist] => 'b

  LList_corec_fun :: "[nat, 'a=>unit+('b item * 'a), 'a] => 'b item"
  LList_corec     :: "['a, 'a => unit + ('b item * 'a)] => 'b item"
  llist_corec     :: "['a, 'a => unit + ('b * 'a)] => 'b llist"

  Lmap       :: ('a item => 'b item) => ('a item => 'b item)
  lmap       :: ('a=>'b) => ('a llist => 'b llist)

  iterates   :: ['a => 'a, 'a] => 'a llist

  Lconst     :: 'a item => 'a item
  Lappend    :: ['a item, 'a item] => 'a item
  lappend    :: ['a llist, 'a llist] => 'a llist


coinductive "llist(A)"
  intrs
    NIL_I  "NIL: llist(A)"
    CONS_I "[| a: A;  M: llist(A) |] ==> CONS a M : llist(A)"

coinductive "LListD(r)"
  intrs
    NIL_I  "(NIL, NIL) : LListD(r)"
    CONS_I "[| (a,b): r;  (M,N) : LListD(r)   
            |] ==> (CONS a M, CONS b N) : LListD(r)"

translations
  "case p of LNil => a | LCons x l => b" == "llist_case a (%x l. b) p"


defs
  (*Now used exclusively for abbreviating the coinduction rule*)
  list_Fun_def   "list_Fun A X ==   
                  {z. z = NIL | (? M a. z = CONS a M & a : A & M : X)}"

  LListD_Fun_def "LListD_Fun r X ==   
                  {z. z = (NIL, NIL) |   
                      (? M N a b. z = (CONS a M, CONS b N) &   
                                  (a, b) : r & (M, N) : X)}"

  (*defining the abstract constructors*)
  LNil_def      "LNil == Abs_llist(NIL)"
  LCons_def     "LCons x xs == Abs_llist(CONS (Leaf x) (Rep_llist xs))"

  llist_case_def
   "llist_case c d l == 
       List_case c (%x y. d (inv Leaf x) (Abs_llist y)) (Rep_llist l)"

  LList_corec_fun_def
    "LList_corec_fun k f == 
     nat_rec (%x. {})                         
             (%j r x. case f x of Inl u    => NIL
                                | Inr(z,w) => CONS z (r w)) 
             k"

  LList_corec_def
    "LList_corec a f == UN k. LList_corec_fun k f a"

  llist_corec_def
   "llist_corec a f == 
       Abs_llist(LList_corec a 
                 (%z. case f z of Inl x    => Inl(x)
                               | Inr(v,w) => Inr(Leaf(v), w)))"

  llistD_Fun_def
   "llistD_Fun(r) ==    
        prod_fun Abs_llist Abs_llist ``         
                LListD_Fun (diag(range Leaf))   
                            (prod_fun Rep_llist Rep_llist `` r)"

  Lconst_def    "Lconst(M) == lfp(%N. CONS M N)"     

  Lmap_def
   "Lmap f M == LList_corec M (List_case (Inl ()) (%x M'. Inr((f(x), M'))))"

  lmap_def
   "lmap f l == llist_corec l (%z. case z of LNil => (Inl ()) 
                                           | LCons y z => Inr(f(y), z))"

  iterates_def  "iterates f a == llist_corec a (%x. Inr((x, f(x))))"     

(*Append generates its result by applying f, where
    f((NIL,NIL))          = Inl(())
    f((NIL, CONS N1 N2))  = Inr((N1, (NIL,N2))
    f((CONS M1 M2, N))    = Inr((M1, (M2,N))
*)

  Lappend_def
   "Lappend M N == LList_corec (M,N)                                         
     (split(List_case (List_case (Inl ()) (%N1 N2. Inr((N1, (NIL,N2))))) 
                      (%M1 M2 N. Inr((M1, (M2,N))))))"

  lappend_def
   "lappend l n == llist_corec (l,n)                                         
   (split(llist_case (llist_case (Inl ()) (%n1 n2. Inr((n1, (LNil,n2))))) 
                     (%l1 l2 n. Inr((l1, (l2,n))))))"

rules
    (*faking a type definition...*)
  Rep_llist         "Rep_llist(xs): llist(range(Leaf))"
  Rep_llist_inverse "Abs_llist(Rep_llist(xs)) = xs"
  Abs_llist_inverse "M: llist(range(Leaf)) ==> Rep_llist(Abs_llist(M)) = M"

end
