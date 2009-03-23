(*  Title:      HOL/Library/Code_Char_chr.thy
    Author:     Florian Haftmann
*)

header {* Code generation of pretty characters with character codes *}

theory Code_Char_chr
imports Char_nat Code_Char Code_Integer Main
begin

definition
  "int_of_char = int o nat_of_char"

lemma [code]:
  "nat_of_char = nat o int_of_char"
  unfolding int_of_char_def by (simp add: expand_fun_eq)

definition
  "char_of_int = char_of_nat o nat"

lemma [code]:
  "char_of_nat = char_of_int o int"
  unfolding char_of_int_def by (simp add: expand_fun_eq)

lemmas [code del] = char.recs char.cases char.size

lemma [code, code inline]:
  "char_rec f c = split f (nibble_pair_of_nat (nat_of_char c))"
  by (cases c) (auto simp add: nibble_pair_of_nat_char)

lemma [code, code inline]:
  "char_case f c = split f (nibble_pair_of_nat (nat_of_char c))"
  by (cases c) (auto simp add: nibble_pair_of_nat_char)

lemma [code]:
  "size (c\<Colon>char) = 0"
  by (cases c) auto

code_const int_of_char and char_of_int
  (SML "!(IntInf.fromInt o Char.ord)" and "!(Char.chr o IntInf.toInt)")
  (OCaml "Big'_int.big'_int'_of'_int (Char.code _)" and "Char.chr (Big'_int.int'_of'_big'_int _)")
  (Haskell "toInteger (fromEnum (_ :: Char))" and "!(let chr k | k < 256 = toEnum k :: Char in chr . fromInteger)")

end