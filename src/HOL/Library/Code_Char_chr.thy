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
  unfolding int_of_char_def by (simp add: fun_eq_iff)

definition
  "char_of_int = char_of_nat o nat"

lemma [code]:
  "char_of_nat = char_of_int o int"
  unfolding char_of_int_def by (simp add: fun_eq_iff)

code_const int_of_char and char_of_int
  (SML "!(IntInf.fromInt o Char.ord)" and "!(Char.chr o IntInf.toInt)")
  (OCaml "Big'_int.big'_int'_of'_int (Char.code _)" and "Char.chr (Big'_int.int'_of'_big'_int _)")
  (Haskell "Prelude.toInteger (Prelude.fromEnum (_ :: Prelude.Char))" and "!(let chr k | (0 <= k && k < 256) = Prelude.toEnum k :: Prelude.Char in chr . Prelude.fromInteger)")
  (Scala "BigInt(_.toInt)" and "!((k: BigInt) => if (BigInt(0) <= k && k < BigInt(256)) k.charValue else error(\"character value out of range\"))")

end
