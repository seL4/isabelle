(*  Title:      HOL/Library/Code_Target_Int.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Implementation of integer numbers by target-language integers *}

theory Code_Target_Int
imports Main "~~/src/HOL/Library/Code_Numeral_Types"
begin

code_datatype int_of_integer

lemma [code, code del]:
  "integer_of_int = integer_of_int" ..

lemma [code]:
  "integer_of_int (int_of_integer k) = k"
  by (simp add: integer_eq_iff)

lemma [code]:
  "Int.Pos = int_of_integer \<circ> integer_of_num"
  by (simp add: integer_of_num_def fun_eq_iff)

lemma [code]:
  "Int.Neg = int_of_integer \<circ> uminus \<circ> integer_of_num"
  by (simp add: integer_of_num_def fun_eq_iff)

lemma [code_abbrev]:
  "int_of_integer (Code_Numeral_Types.Pos k) = Int.Pos k"
  by simp

lemma [code_abbrev]:
  "int_of_integer (Code_Numeral_Types.Neg k) = Int.Neg k"
  by simp

lemma [code]:
  "0 = int_of_integer 0"
  by simp

lemma [code]:
  "1 = int_of_integer 1"
  by simp

lemma [code]:
  "k + l = int_of_integer (of_int k + of_int l)"
  by simp

lemma [code]:
  "- k = int_of_integer (- of_int k)"
  by simp

lemma [code]:
  "k - l = int_of_integer (of_int k - of_int l)"
  by simp

lemma [code]:
  "Int.dup k = int_of_integer (Code_Numeral_Types.dup (of_int k))"
  by simp

lemma [code, code del]:
  "Int.sub = Int.sub" ..

lemma [code]:
  "k * l = int_of_integer (of_int k * of_int l)"
  by simp

lemma [code]:
  "pdivmod k l = map_pair int_of_integer int_of_integer
    (Code_Numeral_Types.divmod_abs (of_int k) (of_int l))"
  by (simp add: prod_eq_iff pdivmod_def)

lemma [code]:
  "k div l = int_of_integer (of_int k div of_int l)"
  by simp

lemma [code]:
  "k mod l = int_of_integer (of_int k mod of_int l)"
  by simp

lemma [code]:
  "HOL.equal k l = HOL.equal (of_int k :: integer) (of_int l)"
  by (simp add: equal integer_eq_iff)

lemma [code]:
  "k \<le> l \<longleftrightarrow> (of_int k :: integer) \<le> of_int l"
  by (simp add: less_eq_int_def)

lemma [code]:
  "k < l \<longleftrightarrow> (of_int k :: integer) < of_int l"
  by (simp add: less_int_def)

lemma (in ring_1) of_int_code:
  "of_int k = (if k = 0 then 0
     else if k < 0 then - of_int (- k)
     else let
       (l, j) = divmod_int k 2;
       l' = 2 * of_int l
     in if j = 0 then l' else l' + 1)"
proof -
  from mod_div_equality have *: "of_int k = of_int (k div 2 * 2 + k mod 2)" by simp
  show ?thesis
    by (simp add: Let_def divmod_int_mod_div mod_2_not_eq_zero_eq_one_int
      of_int_add [symmetric]) (simp add: * mult_commute)
qed

declare of_int_code [code]

lemma [code]:
  "nat = nat_of_integer \<circ> of_int"
  by (simp add: fun_eq_iff nat_of_integer_def)

code_modulename SML
  Code_Target_Int Arith

code_modulename OCaml
  Code_Target_Int Arith

code_modulename Haskell
  Code_Target_Int Arith

end

