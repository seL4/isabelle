(*  Title:      HOL/Main.thy
    ID:         $Id$
*)

header {* Main HOL *}

theory Main
imports Map
begin

text {*
  Theory @{text Main} includes everything.  Note that theory @{text
  PreList} already includes most HOL theories.

  \medskip Late clause setup: installs \emph{all} known theorems
  into the clause cache; cf.\ theory @{text ATP_Linkup}. 
  FIXME: delete once @{text end_theory} actions are installed!
*}

setup ResAxioms.clause_cache_setup

ML {* val HOL_proofs = !proofs *}

end
