(*  Title:      HOL/Univ.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Declares the type 'a node, a subtype of (nat=>nat) * ('a+nat)

Defines "Cartesian Product" and "Disjoint Sum" as set operations.
Could <*> be generalized to a general summation (Sigma)?
*)

Univ = Arith + Sum +

(** lists, trees will be sets of nodes **)

global

typedef (Node)
  'a node = "{p. EX f x k. p = (f::nat=>nat, x::'a+nat) & f(k)=0}"

types
  'a item = 'a node set

consts
  apfst     :: "['a=>'c, 'a*'b] => 'c*'b"
  Push      :: [nat, nat=>nat] => (nat=>nat)

  Push_Node :: [nat, 'a node] => 'a node
  ndepth    :: 'a node => nat

  Atom      :: "('a+nat) => 'a item"
  Leaf      :: 'a => 'a item
  Numb      :: nat => 'a item
  Scons     :: ['a item, 'a item]=> 'a item
  In0,In1   :: 'a item => 'a item

  ntrunc    :: [nat, 'a item] => 'a item

  "<*>"  :: ['a item set, 'a item set]=> 'a item set (infixr 80)
  "<+>"  :: ['a item set, 'a item set]=> 'a item set (infixr 70)

  Split  :: [['a item, 'a item]=>'b, 'a item] => 'b
  Case   :: [['a item]=>'b, ['a item]=>'b, 'a item] => 'b

  "<**>" :: "[('a item * 'a item)set, ('a item * 'a item)set] 
           => ('a item * 'a item)set" (infixr 80)
  "<++>" :: "[('a item * 'a item)set, ('a item * 'a item)set] 
           => ('a item * 'a item)set" (infixr 70)


local

defs

  Push_Node_def  "Push_Node == (%n x. Abs_Node (apfst (Push n) (Rep_Node x)))"

  (*crude "lists" of nats -- needed for the constructions*)
  apfst_def  "apfst == (%f (x,y). (f(x),y))"
  Push_def   "Push == (%b h. nat_case (Suc b) h)"

  (** operations on S-expressions -- sets of nodes **)

  (*S-expression constructors*)
  Atom_def   "Atom == (%x. {Abs_Node((%k.0, x))})"
  Scons_def  "Scons M N == (Push_Node(0) `` M) Un (Push_Node(Suc(0)) `` N)"

  (*Leaf nodes, with arbitrary or nat labels*)
  Leaf_def   "Leaf == Atom o Inl"
  Numb_def   "Numb == Atom o Inr"

  (*Injections of the "disjoint sum"*)
  In0_def    "In0(M) == Scons (Numb 0) M"
  In1_def    "In1(M) == Scons (Numb 1) M"

  (*the set of nodes with depth less than k*)
  ndepth_def "ndepth(n) == (%(f,x). LEAST k. f(k)=0) (Rep_Node n)"
  ntrunc_def "ntrunc k N == {n. n:N & ndepth(n)<k}"

  (*products and sums for the "universe"*)
  uprod_def  "A<*>B == UN x:A. UN y:B. { Scons x y }"
  usum_def   "A<+>B == In0``A Un In1``B"

  (*the corresponding eliminators*)
  Split_def  "Split c M == @u. ? x y. M = Scons x y & u = c x y"

  Case_def   "Case c d M == @u.  (? x . M = In0(x) & u = c(x)) 
                              | (? y . M = In1(y) & u = d(y))"


  (** equality for the "universe" **)

  dprod_def  "r<**>s == UN (x,x'):r. UN (y,y'):s. {(Scons x y, Scons x' y')}"

  dsum_def   "r<++>s == (UN (x,x'):r. {(In0(x),In0(x'))}) Un 
                        (UN (y,y'):s. {(In1(y),In1(y'))})"

end
