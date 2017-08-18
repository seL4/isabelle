(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Pretty syntax for lattice operations\<close>

theory Lattice_Syntax
imports HOL.Complete_Lattices
begin

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) and
  Inf  ("\<Sqinter>_" [900] 900) and
  Sup  ("\<Squnion>_" [900] 900)

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

end
