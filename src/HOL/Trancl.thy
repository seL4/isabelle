(*  Title:      HOL/Trancl.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Relfexive and Transitive closure of a relation

rtrancl is refl&transitive closure;
trancl is transitive closure
reflcl is reflexive closure
*)

Trancl = Lfp + Relation + 
consts
    rtrancl :: "('a * 'a)set => ('a * 'a)set"   ("(_^*)" [100] 100)
    trancl  :: "('a * 'a)set => ('a * 'a)set"   ("(_^+)" [100] 100)  
syntax
    reflcl  :: "('a*'a)set => ('a*'a)set"       ("(_^=)" [100] 100)
defs   
  rtrancl_def   "r^*  ==  lfp(%s. id Un (r O s))"
  trancl_def    "r^+  ==  r O rtrancl(r)"
translations
                "r^=" == "r Un id"
end
