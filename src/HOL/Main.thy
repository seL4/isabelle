(* $Id$ *)

header {* Main HOL *}

theory Main
imports Refute Reconstruction
begin

text {*
  Theory @{text Main} includes everything.  Note that theory @{text
  PreList} already includes most HOL theories.
*}


subsection {* Special hacks, late package setup etc. *}

text {* \medskip Default values for refute, see also theory @{text
  Refute}.
*}

refute_params
 ["itself"=1,
  minsize=1,
  maxsize=8,
  maxvars=10000,
  maxtime=60,
  satsolver="auto"]


text {* \medskip Clause setup: installs \emph{all} simprules and
  claset rules into the clause cache; cf.\ theory @{text
  Reconstruction}. *}

setup ResAxioms.clause_setup

end
