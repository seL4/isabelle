(*  Title:      HOL/Library/Code_Char.thy
    Author:     Florian Haftmann
*)

header {* Code generation of pretty characters (and strings) *}

theory Code_Char
imports List Code_Evaluation Main
begin

code_type char
  (SML "char")
  (OCaml "char")
  (Haskell "Char")
  (Scala "Char")

setup {*
  fold String_Code.add_literal_char ["SML", "OCaml", "Haskell", "Scala"] 
  #> String_Code.add_literal_list_string "Haskell"
*}

code_instance char :: equal
  (Haskell -)

code_reserved SML
  char

code_reserved OCaml
  char

code_reserved Scala
  char

code_const "HOL.equal \<Colon> char \<Rightarrow> char \<Rightarrow> bool"
  (SML "!((_ : char) = _)")
  (OCaml "!((_ : char) = _)")
  (Haskell infixl 4 "==")
  (Scala infixl 5 "==")

code_const "Code_Evaluation.term_of \<Colon> char \<Rightarrow> term"
  (Eval "HOLogic.mk'_char/ (IntInf.fromInt/ (Char.ord/ _))")


definition implode :: "string \<Rightarrow> String.literal" where
  "implode = STR"

primrec explode :: "String.literal \<Rightarrow> string" where
  "explode (STR s) = s"

lemma [code]:
  "literal_case f s = f (explode s)"
  "literal_rec f s = f (explode s)"
  by (cases s, simp)+

code_reserved SML String

code_const implode
  (SML "String.implode")
  (OCaml "failwith/ \"implode\"")
  (Haskell "_")
  (Scala "!(\"\" ++/ _)")

code_const explode
  (SML "String.explode")
  (OCaml "failwith/ \"explode\"")
  (Haskell "_")
  (Scala "!(_.toList)")

end
