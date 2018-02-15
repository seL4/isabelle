(*  Title:      HOL/HOLCF/IOA/Storage/Action.thy
    Author:     Olaf Müller
*)

section \<open>The set of all actions of the system\<close>

theory Action
imports Main
begin

datatype action = New | Loc nat | Free nat

lemma [cong]: "\<And>x. x = y \<Longrightarrow> case_action a b c x = case_action a b c y"
  by simp

end
