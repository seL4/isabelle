(*  Title:      HOL/UNITY/WFair.thy
    ID:         $Id$
    Author:     Sidi Ehmety, Computer Laboratory
    Copyright   1998  University of Cambridge

Weak Fairness versions of transient, ensures, leadsTo.

From Misra, "A Logic for Concurrent Programming", 1994

Theory ported from HOL.
*)

WFair = UNITY +
constdefs
  
  (* This definition specifies weak fairness.  The rest of the theory
    is generic to all forms of fairness.*) 
 transient :: "i=>i"
  "transient(A) =={F:program. (EX act: Acts(F). A<=domain(act) &
			       act``A <= state-A) & st_set(A)}"

  ensures :: "[i,i] => i"       (infixl 60)
  "A ensures B == ((A-B) co (A Un B)) Int transient(A-B)"
  
consts

  (*LEADS-TO constant for the inductive definition*)
  leads :: "[i, i]=>i"

inductive 
  domains
     "leads(D, F)" <= "Pow(D)*Pow(D)"
  intrs 
    Basis  "[| F:A ensures B;  A:Pow(D); B:Pow(D) |] ==> <A,B>:leads(D, F)"
    Trans  "[| <A,B> : leads(D, F); <B,C> : leads(D, F) |] ==>  <A,C>:leads(D, F)"
    Union   "[| S:Pow({A:S. <A, B>:leads(D, F)}); B:Pow(D); S:Pow(Pow(D)) |] ==> 
	      <Union(S),B>:leads(D, F)"

  monos        Pow_mono
  type_intrs  "[Union_PowI, UnionI, PowI]"
 
constdefs

  (* The Visible version of the LEADS-TO relation*)
  leadsTo :: "[i, i] => i"       (infixl 60)
  "A leadsTo B == {F:program. <A,B>:leads(state, F)}"
  
  (* wlt(F, B) is the largest set that leads to B*)
  wlt :: "[i, i] => i"
    "wlt(F, B) == Union({A:Pow(state). F: A leadsTo B})"

syntax (xsymbols)
  "op leadsTo" :: "[i, i] => i" (infixl "\\<longmapsto>" 60)

end
