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
  
  (*This definition specifies weak fairness.  The rest of the theory
    is generic to all forms of fairness.*) 
 transient :: "i=>i"
  "transient(A) =={F:program. (EX act: Acts(F). 
			       A<= domain(act) & act``A <= state-A) & A:condition}"

  ensures :: "[i,i] => i"       (infixl 60)
  "A ensures B == ((A-B) co (A Un B)) Int transient(A-B)"
  
consts

  (*LEADS-TO constant for the inductive definition*)
  leads :: "i=>i"

inductive (* All typing conidition `A:condition' will desapear
             in the dervied rules *)
  domains
     "leads(F)" <= "condition*condition"
  intrs 
    Basis  "[| F:A ensures B; A:condition; B:condition |] ==> <A,B>:leads(F)"
    Trans  "[| <A,B> : leads(F); <B,C> : leads(F) |] ==>  <A,C>:leads(F)"
    Union   "[| S:Pow({A:S. <A, B>:leads(F)});
		B:condition; S:Pow(condition) |] ==> 
	      <Union(S),B>:leads(F)"

  monos        Pow_mono
  type_intrs  "[UnionI, Union_in_conditionI, PowI]"
 
constdefs

  (*visible version of the LEADS-TO relation*)
  leadsTo :: "[i, i] => i"       (infixl 60)
    "A leadsTo B == {F:program.  <A,B>:leads(F)}"
  
  (*wlt F B is the largest set that leads to B*)
  wlt :: "[i, i] => i"
    "wlt(F, B) == Union({A:condition. F: A leadsTo B})"

syntax (xsymbols)
  "op leadsTo" :: "[i, i] => i" (infixl "\\<longmapsto>" 60)

end
