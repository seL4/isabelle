(* Author: Andreas Lochbihler, KIT *)

section \<open>Pretty syntax for almost everywhere constant functions\<close>

theory FinFun_Syntax
imports FinFun
begin

type_notation
  finfun ("(_ \<Rightarrow>f /_)" [22, 21] 21)

notation
  finfun_const ("K$/ _" [0] 1) and
  finfun_update ("_'(_ $:= _')" [1000,0,0] 1000) and
  finfun_apply (infixl "$" 999) and
  finfun_comp (infixr "\<circ>$" 55) and
  finfun_comp2 (infixr "$\<circ>" 55) and
  finfun_Diag ("(1'($_,/ _$'))" [0, 0] 1000)

notation (ASCII)
  finfun_comp (infixr "o$" 55) and
  finfun_comp2 (infixr "$o" 55)

end
