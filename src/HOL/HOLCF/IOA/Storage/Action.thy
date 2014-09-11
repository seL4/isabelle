(*  Title:      HOL/HOLCF/IOA/Storage/Action.thy
    Author:     Olaf Müller
*)

header {* The set of all actions of the system *}

theory Action
imports Main
begin

datatype action = New | Loc nat | Free nat

lemma [cong]: "!!x. x = y ==> case_action a b c x = case_action a b c y"
  by simp

end
