(*  Title:      HOL/BNF/BNF_LFP_Compat.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Compatibility layer with the old datatype package.
*)

header {* Compatibility Layer with the Old Datatype Package *}

theory BNF_LFP_Compat
imports BNF_FP_N2M
keywords
  "datatype_compat" :: thy_goal
begin

ML_file "Tools/bnf_lfp_compat.ML"

end
