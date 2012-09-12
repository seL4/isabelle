(*  Title:      HOL/Codatatype/BNF_GFP.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Greatest fixed point operation on bounded natural functors.
*)

header {* Greatest Fixed Point Operation on Bounded Natural Functors *}

theory BNF_GFP
imports BNF_FP
keywords
  "codata_raw" :: thy_decl and
  "codata" :: thy_decl
begin

ML_file "Tools/bnf_gfp_util.ML"
ML_file "Tools/bnf_gfp_tactics.ML"
ML_file "Tools/bnf_gfp.ML"

end
