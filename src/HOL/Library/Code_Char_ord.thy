(*  Title:      HOL/Library/Code_Char_ord.thy
    Author:     Lukas Bulwahn, Florian Haftmann, Rene Thiemann
*)

header {* Code generation of orderings for pretty characters *}

theory Code_Char_ord
imports Code_Char Char_ord
begin
  
code_const "Orderings.less_eq \<Colon> char \<Rightarrow> char \<Rightarrow> bool"
  (SML "!((_ : char) <= _)")
  (OCaml "!((_ : char) <= _)")
  (Haskell infix 4 "<=")
  (Scala infixl 4 "<=")
  (Eval infixl 6 "<=")

code_const "Orderings.less \<Colon> char \<Rightarrow> char \<Rightarrow> bool"
  (SML "!((_ : char) < _)")
  (OCaml "!((_ : char) < _)")
  (Haskell infix 4 "<")
  (Scala infixl 4 "<")
  (Eval infixl 6 "<")

end