(*  Title: 	HOL/trancl.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Transitive closure of a relation

rtrancl is refl/transitive closure;  trancl is transitive closure
*)

Trancl = Lfp + Prod + 
consts
    trans   :: "('a * 'a)set => bool" 	(*transitivity predicate*)
    id	    :: "('a * 'a)set"
    rtrancl :: "('a * 'a)set => ('a * 'a)set"	("(_^*)" [100] 100)
    trancl  :: "('a * 'a)set => ('a * 'a)set"	("(_^+)" [100] 100)  
    O	    :: "[('b * 'c)set, ('a * 'b)set] => ('a * 'c)set" (infixr 60)
defs   
trans_def	"trans(r) == (!x y z. (x,y):r --> (y,z):r --> (x,z):r)"
comp_def	(*composition of relations*)
		"r O s == {xz. ? x y z. xz = (x,z) & (x,y):s & (y,z):r}"
id_def		(*the identity relation*)
		"id == {p. ? x. p = (x,x)}"
rtrancl_def	"r^* == lfp(%s. id Un (r O s))"
trancl_def	"r^+ == r O rtrancl(r)"
end
