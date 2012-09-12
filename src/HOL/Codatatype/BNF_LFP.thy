(*  Title:      HOL/Codatatype/BNF_LFP.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Least fixed point operation on bounded natural functors.
*)

header {* Least Fixed Point Operation on Bounded Natural Functors *}

theory BNF_LFP
imports BNF_FP
keywords
  "data_raw" :: thy_decl and
  "data" :: thy_decl
begin

ML_file "Tools/bnf_lfp_util.ML"
ML_file "Tools/bnf_lfp_tactics.ML"
ML_file "Tools/bnf_lfp.ML"

end
