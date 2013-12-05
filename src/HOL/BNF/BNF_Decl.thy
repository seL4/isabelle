(*  Title:      HOL/BNF/BNF_Decl.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2013

Axiomatic declaration of bounded natural functors.
*)

header {* Axiomatic declaration of Bounded Natural Functors *}

theory BNF_Decl
imports BNF_Def
keywords
  "bnf_decl" :: thy_decl
begin

ML_file "Tools/bnf_decl.ML"

end
