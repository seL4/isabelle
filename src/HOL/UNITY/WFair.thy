(*  Title:      HOL/UNITY/WFair
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak Fairness versions of transient, ensures, leadsTo.

From Misra, "A Logic for Concurrent Programming", 1994
*)

WFair = UNITY +

constdefs

  (*This definition specifies weak fairness.  The rest of the theory
    is generic to all forms of fairness.*)
  transient :: "'a set => 'a program set"
    "transient A == {F. EX act: Acts F. A <= Domain act & act``A <= -A}"

  ensures :: "['a set, 'a set] => 'a program set"       (infixl 60)
    "A ensures B == (A-B co A Un B) Int transient (A-B)"


consts

  (*LEADS-TO constant for the inductive definition*)
  leads :: "'a program => ('a set * 'a set) set"


inductive "leads F"
  intrs 

    Basis  "F : A ensures B ==> (A,B) : leads F"

    Trans  "[| (A,B) : leads F;  (B,C) : leads F |] ==> (A,C) : leads F"

    Union  "ALL A: S. (A,B) : leads F ==> (Union S, B) : leads F"


constdefs

  (*visible version of the LEADS-TO relation*)
  leadsTo :: "['a set, 'a set] => 'a program set"       (infixl 60)
    "A leadsTo B == {F. (A,B) : leads F}"
  
  (*wlt F B is the largest set that leads to B*)
  wlt :: "['a program, 'a set] => 'a set"
    "wlt F B == Union {A. F: A leadsTo B}"

syntax (xsymbols)
  "op leadsTo" :: "['a set, 'a set] => 'a program set" (infixl "\\<longmapsto>" 60)

end
