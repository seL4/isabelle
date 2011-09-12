(* Title: HOL/Library/Cset_Monad.thy
   Author: Andreas Lochbihler, Karlsruhe Institute of Technology
*)

header {* Monad notation for computable sets (cset) *}

theory Cset_Monad
imports Cset Monad_Syntax 
begin

setup {*
  Adhoc_Overloading.add_variant @{const_name bind} @{const_name Cset.bind}
*}

end