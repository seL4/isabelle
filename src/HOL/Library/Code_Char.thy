(*  Title:      HOL/Library/Code_Char.thy
    Author:     Florian Haftmann
*)

header {* Code generation of pretty characters (and strings) *}

theory Code_Char
imports Main Char_ord
begin

code_printing
  type_constructor char \<rightharpoonup>
    (SML) "char"
    and (OCaml) "char"
    and (Haskell) "Prelude.Char"
    and (Scala) "Char"

setup {*
  fold String_Code.add_literal_char ["SML", "OCaml", "Haskell", "Scala"] 
  #> String_Code.add_literal_list_string "Haskell"
*}

code_printing
  class_instance char :: equal \<rightharpoonup>
    (Haskell) -
| constant "HOL.equal :: char \<Rightarrow> char \<Rightarrow> bool" \<rightharpoonup>
    (SML) "!((_ : char) = _)"
    and (OCaml) "!((_ : char) = _)"
    and (Haskell) infix 4 "=="
    and (Scala) infixl 5 "=="
| constant "Code_Evaluation.term_of \<Colon> char \<Rightarrow> term" \<rightharpoonup>
    (Eval) "HOLogic.mk'_char/ (IntInf.fromInt/ (Char.ord/ _))"

code_reserved SML
  char

code_reserved OCaml
  char

code_reserved Scala
  char

definition implode :: "string \<Rightarrow> String.literal" where
  "implode = STR"

code_reserved SML String

code_printing
  constant implode \<rightharpoonup>
    (SML) "String.implode"
    and (OCaml) "!(let l = _ in let res = String.create (List.length l) in let rec imp i = function | [] -> res | c :: l -> String.set res i c; imp (i + 1) l in imp 0 l)"
    and (Haskell) "_"
    and (Scala) "!(\"\" ++/ _)"
| constant explode \<rightharpoonup>
    (SML) "String.explode"
    and (OCaml) "!(let s = _ in let rec exp i l = if i < 0 then l else exp (i - 1) (String.get s i :: l) in exp (String.length s - 1) [])"
    and (Haskell) "_"
    and (Scala) "!(_.toList)"


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

lemmas integer_of_char_code [code] =
  nat_of_char_simps[
    THEN arg_cong[where f="integer_of_nat"],
    unfolded integer_of_nat_numeral integer_of_nat_1 integer_of_nat_0,
    folded fun_cong[OF integer_of_char_def, unfolded o_apply]]

lemma char_of_integer_code [code]:
  "char_of_integer n = enum_class.enum ! (nat_of_integer n mod 256)"
by(simp add: char_of_integer_def char_of_nat_def)

code_printing
  constant integer_of_char \<rightharpoonup>
    (SML) "!(IntInf.fromInt o Char.ord)"
    and (OCaml) "Big'_int.big'_int'_of'_int (Char.code _)"
    and (Haskell) "Prelude.toInteger (Prelude.fromEnum (_ :: Prelude.Char))"
    and (Scala) "BigInt(_.toInt)"
| constant char_of_integer \<rightharpoonup>
    (SML) "!(Char.chr o IntInf.toInt)"
    and (OCaml) "Char.chr (Big'_int.int'_of'_big'_int _)"
    and (Haskell) "!(let chr k | (0 <= k && k < 256) = Prelude.toEnum k :: Prelude.Char in chr . Prelude.fromInteger)"
    and (Scala) "!((k: BigInt) => if (BigInt(0) <= k && k < BigInt(256)) k.charValue else error(\"character value out of range\"))"
| constant "Orderings.less_eq :: char \<Rightarrow> char \<Rightarrow> bool" \<rightharpoonup>
    (SML) "!((_ : char) <= _)"
    and (OCaml) "!((_ : char) <= _)"
    and (Haskell) infix 4 "<="
    and (Scala) infixl 4 "<="
    and (Eval) infixl 6 "<="
| constant "Orderings.less :: char \<Rightarrow> char \<Rightarrow> bool" \<rightharpoonup>
    (SML) "!((_ : char) < _)"
    and (OCaml) "!((_ : char) < _)"
    and (Haskell) infix 4 "<"
    and (Scala) infixl 4 "<"
    and (Eval) infixl 6 "<"
|  constant "Orderings.less_eq :: String.literal \<Rightarrow> String.literal \<Rightarrow> bool" \<rightharpoonup>
    (SML) "!((_ : string) <= _)"
    and (OCaml) "!((_ : string) <= _)"
    -- {* Order operations for @{typ String.literal} work in Haskell only 
          if no type class instance needs to be generated, because String = [Char] in Haskell
          and @{typ "char list"} need not have the same order as @{typ String.literal}. *}
    and (Haskell) infix 4 "<="
    and (Scala) infixl 4 "<="
    and (Eval) infixl 6 "<="
| constant "Orderings.less :: String.literal \<Rightarrow> String.literal \<Rightarrow> bool" \<rightharpoonup>
    (SML) "!((_ : string) < _)"
    and (OCaml) "!((_ : string) < _)"
    and (Haskell) infix 4 "<"
    and (Scala) infixl 4 "<"
    and (Eval) infixl 6 "<"

end

