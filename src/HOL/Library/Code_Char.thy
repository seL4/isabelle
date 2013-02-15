(*  Title:      HOL/Library/Code_Char.thy
    Author:     Florian Haftmann
*)

header {* Code generation of pretty characters (and strings) *}

theory Code_Char
imports Main "~~/src/HOL/Library/Char_ord"
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


definition integer_of_char :: "char \<Rightarrow> integer"
where
  "integer_of_char = integer_of_nat o nat_of_char"

definition char_of_integer :: "integer \<Rightarrow> char"
where
  "char_of_integer = char_of_nat \<circ> nat_of_integer"

lemma [code]:
  "nat_of_char = nat_of_integer o integer_of_char"
  by (simp add: integer_of_char_def fun_eq_iff)

lemma [code]:
  "char_of_nat = char_of_integer o integer_of_nat"
  by (simp add: char_of_integer_def fun_eq_iff)

code_const integer_of_char and char_of_integer
  (SML "!(IntInf.fromInt o Char.ord)"
    and "!(Char.chr o IntInf.toInt)")
  (OCaml "Big'_int.big'_int'_of'_int (Char.code _)"
    and "Char.chr (Big'_int.int'_of'_big'_int _)")
  (Haskell "Prelude.toInteger (Prelude.fromEnum (_ :: Prelude.Char))"
    and "!(let chr k | (0 <= k && k < 256) = Prelude.toEnum k :: Prelude.Char in chr . Prelude.fromInteger)")
  (Scala "BigInt(_.toInt)"
    and "!((k: BigInt) => if (BigInt(0) <= k && k < BigInt(256)) k.charValue else error(\"character value out of range\"))")


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

