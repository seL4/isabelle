(*  Title:      CCL/Trancl.thy
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header {* Transitive closure of a relation *}

theory Trancl
imports CCL
begin

consts
  trans   :: "i set => o"                   (*transitivity predicate*)
  id      :: "i set"
  rtrancl :: "i set => i set"               ("(_^*)" [100] 100)
  trancl  :: "i set => i set"               ("(_^+)" [100] 100)
  O       :: "[i set,i set] => i set"       (infixr 60)

axioms
  trans_def:       "trans(r) == (ALL x y z. <x,y>:r --> <y,z>:r --> <x,z>:r)"
  comp_def:        (*composition of relations*)
                   "r O s == {xz. EX x y z. xz = <x,z> & <x,y>:s & <y,z>:r}"
  id_def:          (*the identity relation*)
                   "id == {p. EX x. p = <x,x>}"
  rtrancl_def:     "r^* == lfp(%s. id Un (r O s))"
  trancl_def:      "r^+ == r O rtrancl(r)"

ML {* use_legacy_bindings (the_context ()) *}

end
