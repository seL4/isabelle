(*  Title:      HOL/Codatatype/BNF_FP.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Composition of bounded natural functors.
*)

header {* Composition of Bounded Natural Functors *}

theory BNF_FP
imports BNF_Comp BNF_Wrap
keywords
  "defaults"
begin

ML_file "Tools/bnf_fp_util.ML"
ML_file "Tools/bnf_fp_sugar_tactics.ML"
ML_file "Tools/bnf_fp_sugar.ML"

end
