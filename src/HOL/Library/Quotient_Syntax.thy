(*  Title:      HOL/Library/Quotient_Syntax.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Pretty syntax for Quotient operations *}

theory Quotient_Syntax
imports Main
begin

notation
  rel_conj (infixr "OOO" 75) and
  fun_map (infixr "--->" 55) and
  fun_rel (infixr "===>" 55)

end
