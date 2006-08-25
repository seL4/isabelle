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

text {* \medskip Late clause setup: installs \emph{all} known theorems
  into the clause cache; cf.\ theory @{text Reconstruction}. *}

setup ResAxioms.setup

end
