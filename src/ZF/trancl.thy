(*  Title: 	ZF/trancl.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Transitive closure of a relation
*)

Trancl = Fixedpt + Perm + "mono" +
consts
    "rtrancl"	:: "i=>i"  ("(_^*)" [100] 100)  (*refl/transitive closure*)
    "trancl"    :: "i=>i"  ("(_^+)" [100] 100)  (*transitive closure*)
    "trans"	:: "i=>o"  			(*transitivity predicate*)

rules
    trans_def   "trans(r) == ALL x y z. <x,y>: r --> <y,z>: r --> <x,z>: r"

    rtrancl_def	"r^* == lfp(field(r)*field(r), %s. id(field(r)) Un (r O s))"

    trancl_def  "r^+ == r O r^*"
end
