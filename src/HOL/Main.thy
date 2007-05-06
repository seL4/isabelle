(*  Title:      HOL/Main.thy
    ID:         $Id$
*)

header {* Main HOL *}

theory Main
imports Map Hilbert_Choice ATP_Linkup
begin

text {*
  Theory @{text Main} includes everything.  Note that theory @{text
  PreList} already includes most HOL theories.

  \medskip Late clause setup: installs \emph{all} known theorems
  into the clause cache; cf.\ theory @{text ATP_Linkup}.
*}

setup ResAxioms.setup

end
