(*  Title:      HOL/Codatatype/BNF_Wrap.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Wrapping datatypes.
*)

header {* Wrapping Datatypes *}

theory BNF_Wrap
imports BNF_Util
keywords
  "wrap_data" :: thy_goal and
  "no_dests"
begin

ML_file "Tools/bnf_wrap_tactics.ML"
ML_file "Tools/bnf_wrap.ML"

end
