(*  Title:      HOL/SPARK/SPARK.thy
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG

Declaration of proof functions for SPARK/Ada verification environment.
*)

theory SPARK
imports SPARK_Setup
begin

text {* Bitwise logical operators *}

spark_proof_functions
  bit__and (integer, integer) : integer = "op AND"
  bit__or (integer, integer) : integer = "op OR"
  bit__xor (integer, integer) : integer = "op XOR"

lemma AND_lower [simp]:
  fixes x :: int and y :: int
  assumes "0 \<le> x"
  shows "0 \<le> x AND y"
  using assms
proof (induct x arbitrary: y rule: bin_induct)
  case (3 bin bit)
  show ?case
  proof (cases y rule: bin_exhaust)
    case (1 bin' bit')
    from 3 have "0 \<le> bin"
      by (simp add: Bit_def bitval_def split add: bit.split_asm)
    then have "0 \<le> bin AND bin'" by (rule 3)
    with 1 show ?thesis
      by simp (simp add: Bit_def bitval_def split add: bit.split)
  qed
next
  case 2
  then show ?case by (simp only: Min_def)
qed simp

lemma OR_lower [simp]:
  fixes x :: int and y :: int
  assumes "0 \<le> x" "0 \<le> y"
  shows "0 \<le> x OR y"
  using assms
proof (induct x arbitrary: y rule: bin_induct)
  case (3 bin bit)
  show ?case
  proof (cases y rule: bin_exhaust)
    case (1 bin' bit')
    from 3 have "0 \<le> bin"
      by (simp add: Bit_def bitval_def split add: bit.split_asm)
    moreover from 1 3 have "0 \<le> bin'"
      by (simp add: Bit_def bitval_def split add: bit.split_asm)
    ultimately have "0 \<le> bin OR bin'" by (rule 3)
    with 1 show ?thesis
      by simp (simp add: Bit_def bitval_def split add: bit.split)
  qed
qed simp_all

lemma XOR_lower [simp]:
  fixes x :: int and y :: int
  assumes "0 \<le> x" "0 \<le> y"
  shows "0 \<le> x XOR y"
  using assms
proof (induct x arbitrary: y rule: bin_induct)
  case (3 bin bit)
  show ?case
  proof (cases y rule: bin_exhaust)
    case (1 bin' bit')
    from 3 have "0 \<le> bin"
      by (simp add: Bit_def bitval_def split add: bit.split_asm)
    moreover from 1 3 have "0 \<le> bin'"
      by (simp add: Bit_def bitval_def split add: bit.split_asm)
    ultimately have "0 \<le> bin XOR bin'" by (rule 3)
    with 1 show ?thesis
      by simp (simp add: Bit_def bitval_def split add: bit.split)
  qed
next
  case 2
  then show ?case by (simp only: Min_def)
qed simp

lemma AND_upper1 [simp]:
  fixes x :: int and y :: int
  assumes "0 \<le> x"
  shows "x AND y \<le> x"
  using assms
proof (induct x arbitrary: y rule: bin_induct)
  case (3 bin bit)
  show ?case
  proof (cases y rule: bin_exhaust)
    case (1 bin' bit')
    from 3 have "0 \<le> bin"
      by (simp add: Bit_def bitval_def split add: bit.split_asm)
    then have "bin AND bin' \<le> bin" by (rule 3)
    with 1 show ?thesis
      by simp (simp add: Bit_def bitval_def split add: bit.split)
  qed
next
  case 2
  then show ?case by (simp only: Min_def)
qed simp

lemmas AND_upper1' [simp] = order_trans [OF AND_upper1]
lemmas AND_upper1'' [simp] = order_le_less_trans [OF AND_upper1]

lemma AND_upper2 [simp]:
  fixes x :: int and y :: int
  assumes "0 \<le> y"
  shows "x AND y \<le> y"
  using assms
proof (induct y arbitrary: x rule: bin_induct)
  case (3 bin bit)
  show ?case
  proof (cases x rule: bin_exhaust)
    case (1 bin' bit')
    from 3 have "0 \<le> bin"
      by (simp add: Bit_def bitval_def split add: bit.split_asm)
    then have "bin' AND bin \<le> bin" by (rule 3)
    with 1 show ?thesis
      by simp (simp add: Bit_def bitval_def split add: bit.split)
  qed
next
  case 2
  then show ?case by (simp only: Min_def)
qed simp

lemmas AND_upper2' [simp] = order_trans [OF AND_upper2]
lemmas AND_upper2'' [simp] = order_le_less_trans [OF AND_upper2]

lemma OR_upper:
  fixes x :: int and y :: int
  assumes "0 \<le> x" "x < 2 ^ n" "y < 2 ^ n"
  shows "x OR y < 2 ^ n"
  using assms
proof (induct x arbitrary: y n rule: bin_induct)
  case (3 bin bit)
  show ?case
  proof (cases y rule: bin_exhaust)
    case (1 bin' bit')
    show ?thesis
    proof (cases n)
      case 0
      with 3 have "bin BIT bit = 0" by simp
      then have "bin = 0" "bit = 0"
        by (auto simp add: Bit_def bitval_def split add: bit.split_asm) arith
      then show ?thesis using 0 1 `y < 2 ^ n`
        by simp
    next
      case (Suc m)
      from 3 have "0 \<le> bin"
        by (simp add: Bit_def bitval_def split add: bit.split_asm)
      moreover from 3 Suc have "bin < 2 ^ m"
        by (simp add: Bit_def bitval_def split add: bit.split_asm)
      moreover from 1 3 Suc have "bin' < 2 ^ m"
        by (simp add: Bit_def bitval_def split add: bit.split_asm)
      ultimately have "bin OR bin' < 2 ^ m" by (rule 3)
      with 1 Suc show ?thesis
        by simp (simp add: Bit_def bitval_def split add: bit.split)
    qed
  qed
qed simp_all

lemmas [simp] =
  OR_upper [of _ 8, simplified zle_diff1_eq [symmetric], simplified]
  OR_upper [of _ 8, simplified]
  OR_upper [of _ 16, simplified zle_diff1_eq [symmetric], simplified]
  OR_upper [of _ 16, simplified]
  OR_upper [of _ 32, simplified zle_diff1_eq [symmetric], simplified]
  OR_upper [of _ 32, simplified]
  OR_upper [of _ 64, simplified zle_diff1_eq [symmetric], simplified]
  OR_upper [of _ 64, simplified]

lemma XOR_upper:
  fixes x :: int and y :: int
  assumes "0 \<le> x" "x < 2 ^ n" "y < 2 ^ n"
  shows "x XOR y < 2 ^ n"
  using assms
proof (induct x arbitrary: y n rule: bin_induct)
  case (3 bin bit)
  show ?case
  proof (cases y rule: bin_exhaust)
    case (1 bin' bit')
    show ?thesis
    proof (cases n)
      case 0
      with 3 have "bin BIT bit = 0" by simp
      then have "bin = 0" "bit = 0"
        by (auto simp add: Bit_def bitval_def split add: bit.split_asm) arith
      then show ?thesis using 0 1 `y < 2 ^ n`
        by simp
    next
      case (Suc m)
      from 3 have "0 \<le> bin"
        by (simp add: Bit_def bitval_def split add: bit.split_asm)
      moreover from 3 Suc have "bin < 2 ^ m"
        by (simp add: Bit_def bitval_def split add: bit.split_asm)
      moreover from 1 3 Suc have "bin' < 2 ^ m"
        by (simp add: Bit_def bitval_def split add: bit.split_asm)
      ultimately have "bin XOR bin' < 2 ^ m" by (rule 3)
      with 1 Suc show ?thesis
        by simp (simp add: Bit_def bitval_def split add: bit.split)
    qed
  qed
next
  case 2
  then show ?case by (simp only: Min_def)
qed simp

lemmas [simp] =
  XOR_upper [of _ 8, simplified zle_diff1_eq [symmetric], simplified]
  XOR_upper [of _ 8, simplified]
  XOR_upper [of _ 16, simplified zle_diff1_eq [symmetric], simplified]
  XOR_upper [of _ 16, simplified]
  XOR_upper [of _ 32, simplified zle_diff1_eq [symmetric], simplified]
  XOR_upper [of _ 32, simplified]
  XOR_upper [of _ 64, simplified zle_diff1_eq [symmetric], simplified]
  XOR_upper [of _ 64, simplified]

lemma bit_not_spark_eq:
  "NOT (word_of_int x :: ('a::len0) word) =
  word_of_int (2 ^ len_of TYPE('a) - 1 - x)"
proof -
  have "word_of_int x + NOT (word_of_int x) =
    word_of_int x + (word_of_int (2 ^ len_of TYPE('a) - 1 - x)::'a word)"
    by (simp only: bwsimps bin_add_not Min_def)
      (simp add: word_of_int_hom_syms word_of_int_2p_len)
  then show ?thesis by (rule add_left_imp_eq)
qed

lemmas [simp] =
  bit_not_spark_eq [where 'a=8, simplified]
  bit_not_spark_eq [where 'a=16, simplified]
  bit_not_spark_eq [where 'a=32, simplified]
  bit_not_spark_eq [where 'a=64, simplified]

lemma power_BIT: "2 ^ (Suc n) - 1 = (2 ^ n - 1) BIT 1"
  unfolding Bit_B1
  by (induct n) simp_all

lemma mod_BIT:
  "bin BIT bit mod 2 ^ Suc n = (bin mod 2 ^ n) BIT bit"
proof -
  have "bin mod 2 ^ n < 2 ^ n" by simp
  then have "bin mod 2 ^ n \<le> 2 ^ n - 1" by simp
  then have "2 * (bin mod 2 ^ n) \<le> 2 * (2 ^ n - 1)"
    by (rule mult_left_mono) simp
  then have "2 * (bin mod 2 ^ n) + 1 < 2 * 2 ^ n" by simp
  then show ?thesis
    by (auto simp add: Bit_def bitval_def mod_mult_mult1 mod_add_left_eq [of "2 * bin"]
      mod_pos_pos_trivial split add: bit.split)
qed

lemma AND_mod:
  fixes x :: int
  shows "x AND 2 ^ n - 1 = x mod 2 ^ n"
proof (induct x arbitrary: n rule: bin_induct)
  case 1
  then show ?case
    by simp
next
  case 2
  then show ?case
    by (simp, simp add: m1mod2k)
next
  case (3 bin bit)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by (simp add: int_and_extra_simps)
  next
    case (Suc m)
    with 3 show ?thesis
      by (simp only: power_BIT mod_BIT int_and_Bits) simp
  qed
qed

end
