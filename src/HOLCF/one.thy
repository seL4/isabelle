(*  Title: 	HOLCF/one.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Introduve atomic type one = (void)u

This is the first type that is introduced using a domain isomorphism.
The type axiom 

	arities one :: pcpo

and the continuity of the Isomorphisms are taken for granted. Since the
type is not recursive, it could be easily introduced in a purely conservative
style as it was used for the types sprod, ssum, lift. The definition of the 
ordering is canonical using abstraction and representation, but this would take
again a lot of internal constants. It can easily be seen that the axioms below
are consistent.

The partial ordering on type one is implicitly defined via the
isomorphism axioms and the continuity of abs_one and rep_one.

We could also introduce the function less_one with definition

less_one(x,y) = rep_one[x] << rep_one[y]


*)

One = ccc1+

types one 0
arities one :: pcpo

consts
	abs_one		:: "(void)u -> one"
	rep_one		:: "one -> (void)u"
	one 		:: "one"
	one_when 	:: "'c -> one -> 'c"

rules
  abs_one_iso	"abs_one[rep_one[u]] = u"
  rep_one_iso  "rep_one[abs_one[x]] = x"

  one_def	"one == abs_one[up[UU]]"
  one_when_def "one_when == (LAM c u.lift[LAM x.c][rep_one[u]])"

end





