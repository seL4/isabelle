(*  Title: 	ZF/Zorn.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Based upon the article
    Abrial & Laffitte, 
    Towards the Mechanization of the Proofs of Some 
    Classical Theorems of Set Theory. 

Union_in_Pow is proved in ZF.ML
*)

Zorn = OrderArith + AC + "Inductive" +

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


(** We could make the inductive definition conditional on next: increasing(S)
    but instead we make this a side-condition of an introduction rule.  Thus
    the induction rule lets us assume that condition!  Many inductive proofs
    are therefore unconditional.
**)
consts
  "TFin" :: "[i,i]=>i"

inductive
  domains       "TFin(S,next)" <= "Pow(S)"
  intrs
    nextI	"[| x : TFin(S,next);  next: increasing(S) \
\                |] ==> next`x : TFin(S,next)"

    Pow_UnionI	"Y : Pow(TFin(S,next)) ==> Union(Y) : TFin(S,next)"

  monos         "[Pow_mono]"
  con_defs      "[increasing_def]"
  type_intrs    "[CollectD1 RS apply_funtype, Union_in_Pow]"
  
end
