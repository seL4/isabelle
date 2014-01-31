(*  Title:      HOL/Word/Bit_Comparison.thy
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG

Comparison on bit operations on integers.
*)

theory Bit_Comparison
imports Bits_Int
begin

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
      by (cases bit) (simp_all add: Bit_def)
    then have "0 \<le> bin AND bin'" by (rule 3)
    with 1 show ?thesis
      by simp (simp add: Bit_def)
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
      by (cases bit) (simp_all add: Bit_def)
    moreover from 1 3 have "0 \<le> bin'"
      by (cases bit') (simp_all add: Bit_def)
    ultimately have "0 \<le> bin OR bin'" by (rule 3)
    with 1 show ?thesis
      by simp (simp add: Bit_def)
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
      by (cases bit) (simp_all add: Bit_def)
    moreover from 1 3 have "0 \<le> bin'"
      by (cases bit') (simp_all add: Bit_def)
    ultimately have "0 \<le> bin XOR bin'" by (rule 3)
    with 1 show ?thesis
      by simp (simp add: Bit_def)
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
      by (cases bit) (simp_all add: Bit_def)
    then have "bin AND bin' \<le> bin" by (rule 3)
    with 1 show ?thesis
      by simp (simp add: Bit_def)
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
      by (cases bit) (simp_all add: Bit_def)
    then have "bin' AND bin \<le> bin" by (rule 3)
    with 1 show ?thesis
      by simp (simp add: Bit_def)
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
      then have "bin = 0" and "\<not> bit"
        by (auto simp add: Bit_def split: if_splits) arith
      then show ?thesis using 0 1 `y < 2 ^ n`
        by simp
    next
      case (Suc m)
      from 3 have "0 \<le> bin"
        by (cases bit) (simp_all add: Bit_def)
      moreover from 3 Suc have "bin < 2 ^ m"
        by (cases bit) (simp_all add: Bit_def)
      moreover from 1 3 Suc have "bin' < 2 ^ m"
        by (cases bit') (simp_all add: Bit_def)
      ultimately have "bin OR bin' < 2 ^ m" by (rule 3)
      with 1 Suc show ?thesis
        by simp (simp add: Bit_def)
    qed
  qed
qed simp_all

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
      then have "bin = 0" and "\<not> bit"
        by (auto simp add: Bit_def split: if_splits) arith
      then show ?thesis using 0 1 `y < 2 ^ n`
        by simp
    next
      case (Suc m)
      from 3 have "0 \<le> bin"
        by (cases bit) (simp_all add: Bit_def)
      moreover from 3 Suc have "bin < 2 ^ m"
        by (cases bit) (simp_all add: Bit_def)
      moreover from 1 3 Suc have "bin' < 2 ^ m"
        by (cases bit') (simp_all add: Bit_def)
      ultimately have "bin XOR bin' < 2 ^ m" by (rule 3)
      with 1 Suc show ?thesis
        by simp (simp add: Bit_def)
    qed
  qed
next
  case 2
  then show ?case by (simp only: Min_def)
qed simp

end
