(*  Title:      HOL/Library/BNF_Axiomatization.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2013

Axiomatic declaration of bounded natural functors.
*)

section \<open>Axiomatic Declaration of Bounded Natural Functors\<close>

theory BNF_Axiomatization
imports Main
keywords
  "bnf_axiomatization" :: thy_decl
begin

ML_file \<open>../Tools/BNF/bnf_axiomatization.ML\<close>

end
