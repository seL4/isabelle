(*  Title:      HOL/Library/Code_Integer.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Pretty integer literals for code generation *}

theory Code_Integer
imports Main
begin

text {*
  HOL numeral expressions are mapped to integer literals
  in target languages, using predefined target language
  operations for abstract integer operations.
*}

code_type int
  (SML "IntInf.int")
  (OCaml "Big'_int.big'_int")
  (Haskell "Integer")

code_instance int :: eq
  (Haskell -)

setup {*
  fold (Numeral.add_code @{const_name number_int_inst.number_of_int}
    true true) ["SML", "OCaml", "Haskell"]
*}

code_const "Int.Pls" and "Int.Min" and "Int.Bit0" and "Int.Bit1"
  (SML "raise/ Fail/ \"Pls\""
     and "raise/ Fail/ \"Min\""
     and "!((_);/ raise/ Fail/ \"Bit0\")"
     and "!((_);/ raise/ Fail/ \"Bit1\")")
  (OCaml "failwith/ \"Pls\""
     and "failwith/ \"Min\""
     and "!((_);/ failwith/ \"Bit0\")"
     and "!((_);/ failwith/ \"Bit1\")")
  (Haskell "error/ \"Pls\""
     and "error/ \"Min\""
     and "error/ \"Bit0\""
     and "error/ \"Bit1\"")

code_const Int.pred
  (SML "IntInf.- ((_), 1)")
  (OCaml "Big'_int.pred'_big'_int")
  (Haskell "!(_/ -/ 1)")

code_const Int.succ
  (SML "IntInf.+ ((_), 1)")
  (OCaml "Big'_int.succ'_big'_int")
  (Haskell "!(_/ +/ 1)")

code_const "op + \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "IntInf.+ ((_), (_))")
  (OCaml "Big'_int.add'_big'_int")
  (Haskell infixl 6 "+")

code_const "uminus \<Colon> int \<Rightarrow> int"
  (SML "IntInf.~")
  (OCaml "Big'_int.minus'_big'_int")
  (Haskell "negate")

code_const "op - \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "IntInf.- ((_), (_))")
  (OCaml "Big'_int.sub'_big'_int")
  (Haskell infixl 6 "-")

code_const "op * \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "IntInf.* ((_), (_))")
  (OCaml "Big'_int.mult'_big'_int")
  (Haskell infixl 7 "*")

code_const pdivmod
  (SML "(fn k => fn l =>/ IntInf.divMod/ (IntInf.abs k,/ IntInf.abs l))")
  (OCaml "(fun k -> fun l ->/ Big'_int.quomod'_big'_int/ (Big'_int.abs'_big'_int k)/ (Big'_int.abs'_big'_int l))")
  (Haskell "(\\k l ->/ divMod/ (abs k)/ (abs l))")

code_const "eq_class.eq \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "!((_ : IntInf.int) = _)")
  (OCaml "Big'_int.eq'_big'_int")
  (Haskell infixl 4 "==")

code_const "op \<le> \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "IntInf.<= ((_), (_))")
  (OCaml "Big'_int.le'_big'_int")
  (Haskell infix 4 "<=")

code_const "op < \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "IntInf.< ((_), (_))")
  (OCaml "Big'_int.lt'_big'_int")
  (Haskell infix 4 "<")

code_const Code_Numeral.int_of
  (SML "IntInf.fromInt")
  (OCaml "_")
  (Haskell "toEnum")

code_reserved SML IntInf

text {* Evaluation *}

code_const "Code_Evaluation.term_of \<Colon> int \<Rightarrow> term"
  (Eval "HOLogic.mk'_number/ HOLogic.intT")

end