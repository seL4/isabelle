(*  Title: 	ZF/Zorn0.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Based upon the article
    Abrial & Laffitte, 
    Towards the Mechanization of the Proofs of Some 
    Classical Theorems of Set Theory. 
*)

Zorn0 = OrderArith + AC + "inductive" +

consts
  Subset_rel      :: "i=>i"
  increasing      :: "i=>i"
  chain, maxchain :: "i=>i"
  super           :: "[i,i]=>i"

rules
  Subset_rel_def "Subset_rel(A) == {z: A*A . EX x y. z=<x,y> & x<=y & x~=y}"
  increasing_def "increasing(A) == {f: Pow(A)->Pow(A). ALL x. x<=A --> x<=f`x}"

  chain_def      "chain(A)      == {F: Pow(A). ALL X:F. ALL Y:F. X<=Y | Y<=X}"
  super_def      "super(A,c)    == {d: chain(A). c<=d & c~=d}"
  maxchain_def   "maxchain(A)   == {c: chain(A). super(A,c)=0}"

end
