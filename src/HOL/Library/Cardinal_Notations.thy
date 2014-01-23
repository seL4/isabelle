(*  Title:      HOL/Library/Cardinal_Notations.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Cardinal notations.
*)

header {* Cardinal Notations *}

theory Cardinal_Notations
imports Main
begin

notation
  ordLeq2 (infix "<=o" 50) and
  ordLeq3 (infix "\<le>o" 50) and
  ordLess2 (infix "<o" 50) and
  ordIso2 (infix "=o" 50) and
  card_of ("|_|") and
  BNF_Cardinal_Arithmetic.csum (infixr "+c" 65) and
  BNF_Cardinal_Arithmetic.cprod (infixr "*c" 80) and
  BNF_Cardinal_Arithmetic.cexp (infixr "^c" 90)

abbreviation "cinfinite \<equiv> BNF_Cardinal_Arithmetic.cinfinite"
abbreviation "czero \<equiv> BNF_Cardinal_Arithmetic.czero"
abbreviation "cone \<equiv> BNF_Cardinal_Arithmetic.cone"
abbreviation "ctwo \<equiv> BNF_Cardinal_Arithmetic.ctwo"

end
