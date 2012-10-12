(*  Title:      HOL/Library/Bit.thy
    Author:     Brian Huffman
*)

header {* The Field of Integers mod 2 *}

theory Bit
imports Main
begin

subsection {* Bits as a datatype *}

typedef bit = "UNIV :: bool set" ..

instantiation bit :: "{zero, one}"
begin

definition zero_bit_def:
  "0 = Abs_bit False"

definition one_bit_def:
  "1 = Abs_bit True"

instance ..

end

rep_datatype "0::bit" "1::bit"
proof -
  fix P and x :: bit
  assume "P (0::bit)" and "P (1::bit)"
  then have "\<forall>b. P (Abs_bit b)"
    unfolding zero_bit_def one_bit_def
    by (simp add: all_bool_eq)
  then show "P x"
    by (induct x) simp
next
  show "(0::bit) \<noteq> (1::bit)"
    unfolding zero_bit_def one_bit_def
    by (simp add: Abs_bit_inject)
qed

lemma bit_not_0_iff [iff]: "(x::bit) \<noteq> 0 \<longleftrightarrow> x = 1"
  by (induct x) simp_all

lemma bit_not_1_iff [iff]: "(x::bit) \<noteq> 1 \<longleftrightarrow> x = 0"
  by (induct x) simp_all


subsection {* Type @{typ bit} forms a field *}

instantiation bit :: field_inverse_zero
begin

definition plus_bit_def:
  "x + y = bit_case y (bit_case 1 0 y) x"

definition times_bit_def:
  "x * y = bit_case 0 y x"

definition uminus_bit_def [simp]:
  "- x = (x :: bit)"

definition minus_bit_def [simp]:
  "x - y = (x + y :: bit)"

definition inverse_bit_def [simp]:
  "inverse x = (x :: bit)"

definition divide_bit_def [simp]:
  "x / y = (x * y :: bit)"

lemmas field_bit_defs =
  plus_bit_def times_bit_def minus_bit_def uminus_bit_def
  divide_bit_def inverse_bit_def

instance proof
qed (unfold field_bit_defs, auto split: bit.split)

end

lemma bit_add_self: "x + x = (0 :: bit)"
  unfolding plus_bit_def by (simp split: bit.split)

lemma bit_mult_eq_1_iff [simp]: "x * y = (1 :: bit) \<longleftrightarrow> x = 1 \<and> y = 1"
  unfolding times_bit_def by (simp split: bit.split)

text {* Not sure whether the next two should be simp rules. *}

lemma bit_add_eq_0_iff: "x + y = (0 :: bit) \<longleftrightarrow> x = y"
  unfolding plus_bit_def by (simp split: bit.split)

lemma bit_add_eq_1_iff: "x + y = (1 :: bit) \<longleftrightarrow> x \<noteq> y"
  unfolding plus_bit_def by (simp split: bit.split)


subsection {* Numerals at type @{typ bit} *}

text {* All numerals reduce to either 0 or 1. *}

lemma bit_minus1 [simp]: "-1 = (1 :: bit)"
  by (simp only: minus_one [symmetric] uminus_bit_def)

lemma bit_neg_numeral [simp]: "(neg_numeral w :: bit) = numeral w"
  by (simp only: neg_numeral_def uminus_bit_def)

lemma bit_numeral_even [simp]: "numeral (Num.Bit0 w) = (0 :: bit)"
  by (simp only: numeral_Bit0 bit_add_self)

lemma bit_numeral_odd [simp]: "numeral (Num.Bit1 w) = (1 :: bit)"
  by (simp only: numeral_Bit1 bit_add_self add_0_left)

end
