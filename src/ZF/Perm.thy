(*  Title: 	ZF/perm
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

The theory underlying permutation groups
  -- Composition of relations, the identity relation
  -- Injections, surjections, bijections
  -- Lemmas for the Schroeder-Bernstein Theorem
*)

Perm = ZF + "mono" +
consts
    O    	::      "[i,i]=>i"      (infixr 60)
    id  	::      "i=>i"
    inj,surj,bij::      "[i,i]=>i"

rules

    (*composition of relations and functions; NOT Suppes's relative product*)
    comp_def	"r O s == {xz : domain(s)*range(r) . \
\                  		EX x y z. xz=<x,z> & <x,y>:s & <y,z>:r}"

    (*the identity function for A*)
    id_def	"id(A) == (lam x:A. x)"

    (*one-to-one functions from A to B*)
    inj_def      "inj(A,B) == { f: A->B. ALL w:A. ALL x:A. f`w=f`x --> w=x}"

    (*onto functions from A to B*)
    surj_def	"surj(A,B) == { f: A->B . ALL y:B. EX x:A. f`x=y}"

    (*one-to-one and onto functions*)
    bij_def	"bij(A,B) == inj(A,B) Int surj(A,B)"

end
