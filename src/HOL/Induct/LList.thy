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
       (UN x. (split(%l1 l2.(LCons(x,l1),LCons(x,l2))))`r)"
*)

LList = Main + SList +

consts

  llist      :: 'a item set => 'a item set
  LListD     :: "('a item * 'a item)set => ('a item * 'a item)set"


coinductive "llist(A)"
  intrs
    NIL_I  "NIL: llist(A)"
    CONS_I "[| a: A;  M: llist(A) |] ==> CONS a M : llist(A)"

coinductive "LListD(r)"
  intrs
    NIL_I  "(NIL, NIL) : LListD(r)"
    CONS_I "[| (a,b): r;  (M,N) : LListD(r)   
            |] ==> (CONS a M, CONS b N) : LListD(r)"


typedef (LList)
  'a llist = "llist(range Leaf) :: 'a item set" (llist.NIL_I)

constdefs
  (*Now used exclusively for abbreviating the coinduction rule*)
  list_Fun   :: ['a item set, 'a item set] => 'a item set
     "list_Fun A X == {z. z = NIL | (? M a. z = CONS a M & a : A & M : X)}"

  LListD_Fun :: 
      "[('a item * 'a item)set, ('a item * 'a item)set] => 
       ('a item * 'a item)set"
    "LListD_Fun r X ==   
       {z. z = (NIL, NIL) |   
           (? M N a b. z = (CONS a M, CONS b N) & (a, b) : r & (M, N) : X)}"

  (*the abstract constructors*)
  LNil       :: 'a llist
    "LNil == Abs_LList NIL"

  LCons      :: ['a, 'a llist] => 'a llist
    "LCons x xs == Abs_LList(CONS (Leaf x) (Rep_LList xs))"

  llist_case :: ['b, ['a, 'a llist]=>'b, 'a llist] => 'b
    "llist_case c d l == 
       List_case c (%x y. d (inv Leaf x) (Abs_LList y)) (Rep_LList l)"

  LList_corec_fun :: "[nat, 'a=> ('b item * 'a) option, 'a] => 'b item"
    "LList_corec_fun k f == 
     nat_rec (%x. {})                         
             (%j r x. case f x of None    => NIL
                                | Some(z,w) => CONS z (r w)) 
             k"

  LList_corec     :: "['a, 'a => ('b item * 'a) option] => 'b item"
    "LList_corec a f == UN k. LList_corec_fun k f a"

  llist_corec     :: "['a, 'a => ('b * 'a) option] => 'b llist"
    "llist_corec a f == 
       Abs_LList(LList_corec a 
                 (%z. case f z of None      => None
                                | Some(v,w) => Some(Leaf(v), w)))"

  llistD_Fun :: "('a llist * 'a llist)set => ('a llist * 'a llist)set"
    "llistD_Fun(r) ==    
        prod_fun Abs_LList Abs_LList `         
                LListD_Fun (diag(range Leaf))   
                            (prod_fun Rep_LList Rep_LList ` r)"



(*The case syntax for type 'a llist*)
translations
  "case p of LNil => a | LCons x l => b" == "llist_case a (%x l. b) p"


(** Sample function definitions.  Item-based ones start with L ***)

constdefs
  Lmap       :: ('a item => 'b item) => ('a item => 'b item)
    "Lmap f M == LList_corec M (List_case None (%x M'. Some((f(x), M'))))"

  lmap       :: ('a=>'b) => ('a llist => 'b llist)
    "lmap f l == llist_corec l (%z. case z of LNil => None 
                                           | LCons y z => Some(f(y), z))"

  iterates   :: ['a => 'a, 'a] => 'a llist
    "iterates f a == llist_corec a (%x. Some((x, f(x))))"     

  Lconst     :: 'a item => 'a item
    "Lconst(M) == lfp(%N. CONS M N)"     

(*Append generates its result by applying f, where
    f((NIL,NIL))          = None
    f((NIL, CONS N1 N2))  = Some((N1, (NIL,N2))
    f((CONS M1 M2, N))    = Some((M1, (M2,N))
*)

  Lappend    :: ['a item, 'a item] => 'a item
   "Lappend M N == LList_corec (M,N)                                         
     (split(List_case (List_case None (%N1 N2. Some((N1, (NIL,N2))))) 
                      (%M1 M2 N. Some((M1, (M2,N))))))"

  lappend    :: ['a llist, 'a llist] => 'a llist
    "lappend l n == llist_corec (l,n)                                         
       (split(llist_case (llist_case None (%n1 n2. Some((n1, (LNil,n2))))) 
                         (%l1 l2 n. Some((l1, (l2,n))))))"

end
