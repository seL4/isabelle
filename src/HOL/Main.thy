(*  Title:      HOL/Main.thy
    ID:         $Id$
*)

header {* Main HOL *}

theory Main
imports SAT Reconstruction ResAtpMethods
begin

text {*
  Theory @{text Main} includes everything.  Note that theory @{text
  PreList} already includes most HOL theories.
*}


text {* \medskip Late clause setup: installs \emph{all} simprules and
  claset rules into the clause cache; cf.\ theory @{text
  Reconstruction}. *}

declare subset_refl [intro] 
  text {*Ensures that this important theorem is not superseded by the
         simplifier's "== True" version.*}
setup ResAxioms.clause_setup
declare subset_refl [rule del]
  text {*Removed again because it harms blast's performance.*}

end
