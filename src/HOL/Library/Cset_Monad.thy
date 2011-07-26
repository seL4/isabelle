(* Author: Andreas Lochbihler, KIT *)

header {* Add monad syntax for Csets *}

theory Cset_Monad
imports Cset Monad_Syntax 
begin

setup {*
  Adhoc_Overloading.add_variant @{const_name bind} @{const_name Cset.bind}
*}

end