(*  Title:      HOL/Statespace/StateSpaceSyntax.thy
    Author:     Norbert Schirmer, TU Muenchen
*)

section \<open>Syntax for State Space Lookup and Update \label{sec:StateSpaceSyntax}\<close>
theory StateSpaceSyntax
imports StateSpaceLocale
begin

text \<open>The state space syntax is kept in an extra theory so that you
can choose if you want to use it or not.\<close>

syntax 
  "_statespace_lookup" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c"  (\<open>_\<cdot>_\<close> [60, 60] 60)
  "_statespace_update" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> ('a \<Rightarrow> 'b)"
  "_statespace_updates" :: "('a \<Rightarrow> 'b) \<Rightarrow> updbinds \<Rightarrow> ('a \<Rightarrow> 'b)"  (\<open>_<_>\<close> [900, 0] 900)

translations
  "_statespace_updates f (_updbinds b bs)" ==
    "_statespace_updates (_statespace_updates f b) bs"
  "s<x:=y>" == "_statespace_update s x y"


parse_translation
\<open>
 [(\<^syntax_const>\<open>_statespace_lookup\<close>, StateSpace.lookup_tr),
  (\<^syntax_const>\<open>_statespace_update\<close>, StateSpace.update_tr)]
\<close>


print_translation
\<open>
 [(\<^const_syntax>\<open>lookup\<close>, StateSpace.lookup_tr'),
  (\<^const_syntax>\<open>update\<close>, StateSpace.update_tr')]
\<close>

end
