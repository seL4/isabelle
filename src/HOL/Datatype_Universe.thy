(*  Title:      HOL/Datatype_Universe.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Declares the type ('a, 'b) node, a subtype of (nat=>'b+nat) * ('a+nat)

Defines "Cartesian Product" and "Disjoint Sum" as set operations.
Could <*> be generalized to a general summation (Sigma)?
*)

Datatype_Universe = Arithmetic + Sum_Type +


(** lists, trees will be sets of nodes **)

typedef (Node)
  ('a, 'b) node = "{p. EX f x k. p = (f::nat=>'b+nat, x::'a+nat) & f k = Inr 0}"

types
  'a item = ('a, unit) node set
  ('a, 'b) dtree = ('a, 'b) node set

consts
  apfst     :: "['a=>'c, 'a*'b] => 'c*'b"
  Push      :: "[('b + nat), nat => ('b + nat)] => (nat => ('b + nat))"

  Push_Node :: "[('b + nat), ('a, 'b) node] => ('a, 'b) node"
  ndepth    :: ('a, 'b) node => nat

  Atom      :: "('a + nat) => ('a, 'b) dtree"
  Leaf      :: 'a => ('a, 'b) dtree
  Numb      :: nat => ('a, 'b) dtree
  Scons     :: [('a, 'b) dtree, ('a, 'b) dtree] => ('a, 'b) dtree
  In0,In1   :: ('a, 'b) dtree => ('a, 'b) dtree

  Lim       :: ('b => ('a, 'b) dtree) => ('a, 'b) dtree
  Funs      :: "'u set => ('t => 'u) set"

  ntrunc    :: [nat, ('a, 'b) dtree] => ('a, 'b) dtree

  uprod     :: [('a, 'b) dtree set, ('a, 'b) dtree set]=> ('a, 'b) dtree set
  usum      :: [('a, 'b) dtree set, ('a, 'b) dtree set]=> ('a, 'b) dtree set

  Split     :: [[('a, 'b) dtree, ('a, 'b) dtree]=>'c, ('a, 'b) dtree] => 'c
  Case      :: [[('a, 'b) dtree]=>'c, [('a, 'b) dtree]=>'c, ('a, 'b) dtree] => 'c

  dprod     :: "[(('a, 'b) dtree * ('a, 'b) dtree)set, (('a, 'b) dtree * ('a, 'b) dtree)set] 
                => (('a, 'b) dtree * ('a, 'b) dtree)set"
  dsum      :: "[(('a, 'b) dtree * ('a, 'b) dtree)set, (('a, 'b) dtree * ('a, 'b) dtree)set] 
                => (('a, 'b) dtree * ('a, 'b) dtree)set"


defs

  Push_Node_def  "Push_Node == (%n x. Abs_Node (apfst (Push n) (Rep_Node x)))"

  (*crude "lists" of nats -- needed for the constructions*)
  apfst_def  "apfst == (%f (x,y). (f(x),y))"
  Push_def   "Push == (%b h. nat_case b h)"

  (** operations on S-expressions -- sets of nodes **)

  (*S-expression constructors*)
  Atom_def   "Atom == (%x. {Abs_Node((%k. Inr 0, x))})"
  Scons_def  "Scons M N == (Push_Node (Inr 1) `` M) Un (Push_Node (Inr 2) `` N)"

  (*Leaf nodes, with arbitrary or nat labels*)
  Leaf_def   "Leaf == Atom o Inl"
  Numb_def   "Numb == Atom o Inr"

  (*Injections of the "disjoint sum"*)
  In0_def    "In0(M) == Scons (Numb 0) M"
  In1_def    "In1(M) == Scons (Numb 1) M"

  (*Function spaces*)
  Lim_def "Lim f == Union {z. ? x. z = Push_Node (Inl x) `` (f x)}"
  Funs_def "Funs S == {f. range f <= S}"

  (*the set of nodes with depth less than k*)
  ndepth_def "ndepth(n) == (%(f,x). LEAST k. f k = Inr 0) (Rep_Node n)"
  ntrunc_def "ntrunc k N == {n. n:N & ndepth(n)<k}"

  (*products and sums for the "universe"*)
  uprod_def  "uprod A B == UN x:A. UN y:B. { Scons x y }"
  usum_def   "usum A B == In0``A Un In1``B"

  (*the corresponding eliminators*)
  Split_def  "Split c M == @u. ? x y. M = Scons x y & u = c x y"

  Case_def   "Case c d M == @u.  (? x . M = In0(x) & u = c(x)) 
                               | (? y . M = In1(y) & u = d(y))"


  (** equality for the "universe" **)

  dprod_def  "dprod r s == UN (x,x'):r. UN (y,y'):s. {(Scons x y, Scons x' y')}"

  dsum_def   "dsum r s == (UN (x,x'):r. {(In0(x),In0(x'))}) Un 
                          (UN (y,y'):s. {(In1(y),In1(y'))})"

end
