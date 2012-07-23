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
  (Haskell "Prelude.Char")
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
  (Haskell infix 4 "==")
  (Scala infixl 5 "==")

code_const "Code_Evaluation.term_of \<Colon> char \<Rightarrow> term"
  (Eval "HOLogic.mk'_char/ (IntInf.fromInt/ (Char.ord/ _))")


definition implode :: "string \<Rightarrow> String.literal" where
  "implode = STR"

code_reserved SML String

code_const implode
  (SML "String.implode")
  (OCaml "!(let l = _ in let res = String.create (List.length l) in let rec imp i = function | [] -> res | c :: l -> String.set res i c; imp (i + 1) l in imp 0 l)")
  (Haskell "_")
  (Scala "!(\"\" ++/ _)")

code_const explode
  (SML "String.explode")
  (OCaml "!(let s = _ in let rec exp i l = if i < 0 then l else exp (i - 1) (String.get s i :: l) in exp (String.length s - 1) [])")
  (Haskell "_")
  (Scala "!(_.toList)")

end
