(*  Title: 	HOLCF/tr1.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Introduve the domain of truth values tr = {UU,TT,FF}

This type is introduced using a domain isomorphism.

The type axiom 

	arities tr :: pcpo

and the continuity of the Isomorphisms are taken for granted. Since the
type is not recursive, it could be easily introduced in a purely conservative
style as it was used for the types sprod, ssum, lift. The definition of the 
ordering is canonical using abstraction and representation, but this would take
again a lot of internal constants. It can be easily seen that the axioms below
are consistent.

Partial Ordering is implicit in isomorphims abs_tr,rep_tr and their continuity

*)

Tr1 = One +

types tr 0
arities tr :: pcpo

consts
	abs_tr		:: "one ++ one -> tr"
	rep_tr		:: "tr -> one ++ one"
	TT 		:: "tr"
	FF		:: "tr"
	tr_when 	:: "'c -> 'c -> tr -> 'c"

rules

  abs_tr_iso	"abs_tr[rep_tr[u]] = u"
  rep_tr_iso	"rep_tr[abs_tr[x]] = x"

  TT_def	"TT == abs_tr[sinl[one]]"
  FF_def	"FF == abs_tr[sinr[one]]"

  tr_when_def "tr_when == (LAM e1 e2 t.when[LAM x.e1][LAM y.e2][rep_tr[t]])"

end










