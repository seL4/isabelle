(*  Title:      HOL/Library/Pretty_Int.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Pretty integer literals for code generation *}

theory Pretty_Int
imports IntArith
begin

text {*
  HOL numeral expressions are mapped to integer literals
  in target languages, using predefined target language
  operations for abstract integer operations.
*}

code_type int
  (SML "int")
  (OCaml "Big'_int.big'_int")
  (Haskell "Integer")

code_instance int :: eq
  (Haskell -)

setup {*
  fold (fn target => CodeTarget.add_pretty_numeral target true
    @{const_name number_int_inst.number_of_int}
    @{const_name Numeral.B0} @{const_name Numeral.B1}
    @{const_name Numeral.Pls} @{const_name Numeral.Min}
    @{const_name Numeral.Bit}
  ) ["SML", "OCaml", "Haskell"]
*}

code_const "Numeral.Pls" and "Numeral.Min" and "Numeral.Bit"
  (SML "raise/ Fail/ \"Pls\""
     and "raise/ Fail/ \"Min\""
     and "!((_);/ (_);/ raise/ Fail/ \"Bit\")")
  (OCaml "failwith/ \"Pls\""
     and "failwith/ \"Min\""
     and "!((_);/ (_);/ failwith/ \"Bit\")")
  (Haskell "error/ \"Pls\""
     and "error/ \"Min\""
     and "error/ \"Bit\"")

code_const Numeral.pred
  (SML "Int.- ((_), 1)")
  (OCaml "Big'_int.pred'_big'_int")
  (Haskell "!(_/ -/ 1)")

code_const Numeral.succ
  (SML "Int.+ ((_), 1)")
  (OCaml "Big'_int.succ'_big'_int")
  (Haskell "!(_/ +/ 1)")

code_const "op + \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "Int.+ ((_), (_))")
  (OCaml "Big'_int.add'_big'_int")
  (Haskell infixl 6 "+")

code_const "uminus \<Colon> int \<Rightarrow> int"
  (SML "Int.~")
  (OCaml "Big'_int.minus'_big'_int")
  (Haskell "negate")

code_const "op - \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "Int.- ((_), (_))")
  (OCaml "Big'_int.sub'_big'_int")
  (Haskell infixl 6 "-")

code_const "op * \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "Int.* ((_), (_))")
  (OCaml "Big'_int.mult'_big'_int")
  (Haskell infixl 7 "*")

code_const "op = \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "!((_ : Int.int) = _)")
  (OCaml "Big'_int.eq'_big'_int")
  (Haskell infixl 4 "==")

code_const "op \<le> \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "Int.<= ((_), (_))")
  (OCaml "Big'_int.le'_big'_int")
  (Haskell infix 4 "<=")

code_const "op < \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "Int.< ((_), (_))")
  (OCaml "Big'_int.lt'_big'_int")
  (Haskell infix 4 "<")

code_reserved SML Int
code_reserved OCaml Big_int

end