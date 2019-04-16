(*  Title:      HOL/Word/Bits_Int.thy
    Author:     Jeremy Dawson and Gerwin Klein, NICTA

Definitions and basic theorems for bit-wise logical operations
for integers expressed using Pls, Min, BIT,
and converting them to and from lists of bools.
*)

section \<open>Bitwise Operations on Binary Integers\<close>

theory Bits_Int
  imports Bits Bit_Representation Bool_List_Representation
begin

subsection \<open>Logical operations\<close>

text "bit-wise logical operations on the int type"

instantiation int :: bit
begin

definition int_not_def: "bitNOT = (\<lambda>x::int. - x - 1)"

function bitAND_int
  where "bitAND_int x y =
    (if x = 0 then 0 else if x = -1 then y
     else (bin_rest x AND bin_rest y) BIT (bin_last x \<and> bin_last y))"
  by pat_completeness simp

termination
  by (relation "measure (nat \<circ> abs \<circ> fst)", simp_all add: bin_rest_def)

declare bitAND_int.simps [simp del]

definition int_or_def: "bitOR = (\<lambda>x y::int. NOT (NOT x AND NOT y))"

definition int_xor_def: "bitXOR = (\<lambda>x y::int. (x AND NOT y) OR (NOT x AND y))"

instance ..

end

subsubsection \<open>Basic simplification rules\<close>

lemma int_not_BIT [simp]: "NOT (w BIT b) = (NOT w) BIT (\<not> b)"
  by (cases b) (simp_all add: int_not_def Bit_def)

lemma int_not_simps [simp]:
  "NOT (0::int) = -1"
  "NOT (1::int) = -2"
  "NOT (- 1::int) = 0"
  "NOT (numeral w::int) = - numeral (w + Num.One)"
  "NOT (- numeral (Num.Bit0 w)::int) = numeral (Num.BitM w)"
  "NOT (- numeral (Num.Bit1 w)::int) = numeral (Num.Bit0 w)"
  unfolding int_not_def by simp_all

lemma int_not_not [simp]: "NOT (NOT x) = x"
  for x :: int
  unfolding int_not_def by simp

lemma int_and_0 [simp]: "0 AND x = 0"
  for x :: int
  by (simp add: bitAND_int.simps)

lemma int_and_m1 [simp]: "-1 AND x = x"
  for x :: int
  by (simp add: bitAND_int.simps)

lemma int_and_Bits [simp]: "(x BIT b) AND (y BIT c) = (x AND y) BIT (b \<and> c)"
  by (subst bitAND_int.simps) (simp add: Bit_eq_0_iff Bit_eq_m1_iff)

lemma int_or_zero [simp]: "0 OR x = x"
  for x :: int
  by (simp add: int_or_def)

lemma int_or_minus1 [simp]: "-1 OR x = -1"
  for x :: int
  by (simp add: int_or_def)

lemma int_or_Bits [simp]: "(x BIT b) OR (y BIT c) = (x OR y) BIT (b \<or> c)"
  by (simp add: int_or_def)

lemma int_xor_zero [simp]: "0 XOR x = x"
  for x :: int
  by (simp add: int_xor_def)

lemma int_xor_Bits [simp]: "(x BIT b) XOR (y BIT c) = (x XOR y) BIT ((b \<or> c) \<and> \<not> (b \<and> c))"
  unfolding int_xor_def by auto


subsubsection \<open>Binary destructors\<close>

lemma bin_rest_NOT [simp]: "bin_rest (NOT x) = NOT (bin_rest x)"
  by (cases x rule: bin_exhaust) simp

lemma bin_last_NOT [simp]: "bin_last (NOT x) \<longleftrightarrow> \<not> bin_last x"
  by (cases x rule: bin_exhaust) simp

lemma bin_rest_AND [simp]: "bin_rest (x AND y) = bin_rest x AND bin_rest y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust) simp

lemma bin_last_AND [simp]: "bin_last (x AND y) \<longleftrightarrow> bin_last x \<and> bin_last y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust) simp

lemma bin_rest_OR [simp]: "bin_rest (x OR y) = bin_rest x OR bin_rest y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust) simp

lemma bin_last_OR [simp]: "bin_last (x OR y) \<longleftrightarrow> bin_last x \<or> bin_last y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust) simp

lemma bin_rest_XOR [simp]: "bin_rest (x XOR y) = bin_rest x XOR bin_rest y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust) simp

lemma bin_last_XOR [simp]:
  "bin_last (x XOR y) \<longleftrightarrow> (bin_last x \<or> bin_last y) \<and> \<not> (bin_last x \<and> bin_last y)"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust) simp

lemma bin_nth_ops:
  "\<And>x y. bin_nth (x AND y) n \<longleftrightarrow> bin_nth x n \<and> bin_nth y n"
  "\<And>x y. bin_nth (x OR y) n \<longleftrightarrow> bin_nth x n \<or> bin_nth y n"
  "\<And>x y. bin_nth (x XOR y) n \<longleftrightarrow> bin_nth x n \<noteq> bin_nth y n"
  "\<And>x. bin_nth (NOT x) n \<longleftrightarrow> \<not> bin_nth x n"
  by (induct n) auto


subsubsection \<open>Derived properties\<close>

lemma int_xor_minus1 [simp]: "-1 XOR x = NOT x"
  for x :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_xor_extra_simps [simp]:
  "w XOR 0 = w"
  "w XOR -1 = NOT w"
  for w :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_or_extra_simps [simp]:
  "w OR 0 = w"
  "w OR -1 = -1"
  for w :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_and_extra_simps [simp]:
  "w AND 0 = 0"
  "w AND -1 = w"
  for w :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

text \<open>Commutativity of the above.\<close>
lemma bin_ops_comm:
  fixes x y :: int
  shows int_and_comm: "x AND y = y AND x"
    and int_or_comm:  "x OR y = y OR x"
    and int_xor_comm: "x XOR y = y XOR x"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bin_ops_same [simp]:
  "x AND x = x"
  "x OR x = x"
  "x XOR x = 0"
  for x :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemmas bin_log_esimps =
  int_and_extra_simps  int_or_extra_simps  int_xor_extra_simps
  int_and_0 int_and_m1 int_or_zero int_or_minus1 int_xor_zero int_xor_minus1


subsubsection \<open>Basic properties of logical (bit-wise) operations\<close>

lemma bbw_ao_absorb: "x AND (y OR x) = x \<and> x OR (y AND x) = x"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_ao_absorbs_other:
  "x AND (x OR y) = x \<and> (y AND x) OR x = x"
  "(y OR x) AND x = x \<and> x OR (x AND y) = x"
  "(x OR y) AND x = x \<and> (x AND y) OR x = x"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemmas bbw_ao_absorbs [simp] = bbw_ao_absorb bbw_ao_absorbs_other

lemma int_xor_not: "(NOT x) XOR y = NOT (x XOR y) \<and> x XOR (NOT y) = NOT (x XOR y)"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_and_assoc: "(x AND y) AND z = x AND (y AND z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_or_assoc: "(x OR y) OR z = x OR (y OR z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_xor_assoc: "(x XOR y) XOR z = x XOR (y XOR z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemmas bbw_assocs = int_and_assoc int_or_assoc int_xor_assoc

(* BH: Why are these declared as simp rules??? *)
lemma bbw_lcs [simp]:
  "y AND (x AND z) = x AND (y AND z)"
  "y OR (x OR z) = x OR (y OR z)"
  "y XOR (x XOR z) = x XOR (y XOR z)"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_not_dist:
  "NOT (x OR y) = (NOT x) AND (NOT y)"
  "NOT (x AND y) = (NOT x) OR (NOT y)"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_oa_dist: "(x AND y) OR z = (x OR z) AND (y OR z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_ao_dist: "(x OR y) AND z = (x AND z) OR (y AND z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

(*
Why were these declared simp???
declare bin_ops_comm [simp] bbw_assocs [simp]
*)


subsubsection \<open>Simplification with numerals\<close>

text \<open>Cases for \<open>0\<close> and \<open>-1\<close> are already covered by other simp rules.\<close>

lemma bin_rl_eqI: "\<lbrakk>bin_rest x = bin_rest y; bin_last x = bin_last y\<rbrakk> \<Longrightarrow> x = y"
  by (metis (mono_tags) BIT_eq_iff bin_ex_rl bin_last_BIT bin_rest_BIT)

lemma bin_rest_neg_numeral_BitM [simp]:
  "bin_rest (- numeral (Num.BitM w)) = - numeral w"
  by (simp only: BIT_bin_simps [symmetric] bin_rest_BIT)

lemma bin_last_neg_numeral_BitM [simp]:
  "bin_last (- numeral (Num.BitM w))"
  by (simp only: BIT_bin_simps [symmetric] bin_last_BIT)

(* FIXME: The rule sets below are very large (24 rules for each
  operator). Is there a simpler way to do this? *)

lemma int_and_numerals [simp]:
  "numeral (Num.Bit0 x) AND numeral (Num.Bit0 y) = (numeral x AND numeral y) BIT False"
  "numeral (Num.Bit0 x) AND numeral (Num.Bit1 y) = (numeral x AND numeral y) BIT False"
  "numeral (Num.Bit1 x) AND numeral (Num.Bit0 y) = (numeral x AND numeral y) BIT False"
  "numeral (Num.Bit1 x) AND numeral (Num.Bit1 y) = (numeral x AND numeral y) BIT True"
  "numeral (Num.Bit0 x) AND - numeral (Num.Bit0 y) = (numeral x AND - numeral y) BIT False"
  "numeral (Num.Bit0 x) AND - numeral (Num.Bit1 y) = (numeral x AND - numeral (y + Num.One)) BIT False"
  "numeral (Num.Bit1 x) AND - numeral (Num.Bit0 y) = (numeral x AND - numeral y) BIT False"
  "numeral (Num.Bit1 x) AND - numeral (Num.Bit1 y) = (numeral x AND - numeral (y + Num.One)) BIT True"
  "- numeral (Num.Bit0 x) AND numeral (Num.Bit0 y) = (- numeral x AND numeral y) BIT False"
  "- numeral (Num.Bit0 x) AND numeral (Num.Bit1 y) = (- numeral x AND numeral y) BIT False"
  "- numeral (Num.Bit1 x) AND numeral (Num.Bit0 y) = (- numeral (x + Num.One) AND numeral y) BIT False"
  "- numeral (Num.Bit1 x) AND numeral (Num.Bit1 y) = (- numeral (x + Num.One) AND numeral y) BIT True"
  "- numeral (Num.Bit0 x) AND - numeral (Num.Bit0 y) = (- numeral x AND - numeral y) BIT False"
  "- numeral (Num.Bit0 x) AND - numeral (Num.Bit1 y) = (- numeral x AND - numeral (y + Num.One)) BIT False"
  "- numeral (Num.Bit1 x) AND - numeral (Num.Bit0 y) = (- numeral (x + Num.One) AND - numeral y) BIT False"
  "- numeral (Num.Bit1 x) AND - numeral (Num.Bit1 y) = (- numeral (x + Num.One) AND - numeral (y + Num.One)) BIT True"
  "(1::int) AND numeral (Num.Bit0 y) = 0"
  "(1::int) AND numeral (Num.Bit1 y) = 1"
  "(1::int) AND - numeral (Num.Bit0 y) = 0"
  "(1::int) AND - numeral (Num.Bit1 y) = 1"
  "numeral (Num.Bit0 x) AND (1::int) = 0"
  "numeral (Num.Bit1 x) AND (1::int) = 1"
  "- numeral (Num.Bit0 x) AND (1::int) = 0"
  "- numeral (Num.Bit1 x) AND (1::int) = 1"
  by (rule bin_rl_eqI; simp)+

lemma int_or_numerals [simp]:
  "numeral (Num.Bit0 x) OR numeral (Num.Bit0 y) = (numeral x OR numeral y) BIT False"
  "numeral (Num.Bit0 x) OR numeral (Num.Bit1 y) = (numeral x OR numeral y) BIT True"
  "numeral (Num.Bit1 x) OR numeral (Num.Bit0 y) = (numeral x OR numeral y) BIT True"
  "numeral (Num.Bit1 x) OR numeral (Num.Bit1 y) = (numeral x OR numeral y) BIT True"
  "numeral (Num.Bit0 x) OR - numeral (Num.Bit0 y) = (numeral x OR - numeral y) BIT False"
  "numeral (Num.Bit0 x) OR - numeral (Num.Bit1 y) = (numeral x OR - numeral (y + Num.One)) BIT True"
  "numeral (Num.Bit1 x) OR - numeral (Num.Bit0 y) = (numeral x OR - numeral y) BIT True"
  "numeral (Num.Bit1 x) OR - numeral (Num.Bit1 y) = (numeral x OR - numeral (y + Num.One)) BIT True"
  "- numeral (Num.Bit0 x) OR numeral (Num.Bit0 y) = (- numeral x OR numeral y) BIT False"
  "- numeral (Num.Bit0 x) OR numeral (Num.Bit1 y) = (- numeral x OR numeral y) BIT True"
  "- numeral (Num.Bit1 x) OR numeral (Num.Bit0 y) = (- numeral (x + Num.One) OR numeral y) BIT True"
  "- numeral (Num.Bit1 x) OR numeral (Num.Bit1 y) = (- numeral (x + Num.One) OR numeral y) BIT True"
  "- numeral (Num.Bit0 x) OR - numeral (Num.Bit0 y) = (- numeral x OR - numeral y) BIT False"
  "- numeral (Num.Bit0 x) OR - numeral (Num.Bit1 y) = (- numeral x OR - numeral (y + Num.One)) BIT True"
  "- numeral (Num.Bit1 x) OR - numeral (Num.Bit0 y) = (- numeral (x + Num.One) OR - numeral y) BIT True"
  "- numeral (Num.Bit1 x) OR - numeral (Num.Bit1 y) = (- numeral (x + Num.One) OR - numeral (y + Num.One)) BIT True"
  "(1::int) OR numeral (Num.Bit0 y) = numeral (Num.Bit1 y)"
  "(1::int) OR numeral (Num.Bit1 y) = numeral (Num.Bit1 y)"
  "(1::int) OR - numeral (Num.Bit0 y) = - numeral (Num.BitM y)"
  "(1::int) OR - numeral (Num.Bit1 y) = - numeral (Num.Bit1 y)"
  "numeral (Num.Bit0 x) OR (1::int) = numeral (Num.Bit1 x)"
  "numeral (Num.Bit1 x) OR (1::int) = numeral (Num.Bit1 x)"
  "- numeral (Num.Bit0 x) OR (1::int) = - numeral (Num.BitM x)"
  "- numeral (Num.Bit1 x) OR (1::int) = - numeral (Num.Bit1 x)"
  by (rule bin_rl_eqI; simp)+

lemma int_xor_numerals [simp]:
  "numeral (Num.Bit0 x) XOR numeral (Num.Bit0 y) = (numeral x XOR numeral y) BIT False"
  "numeral (Num.Bit0 x) XOR numeral (Num.Bit1 y) = (numeral x XOR numeral y) BIT True"
  "numeral (Num.Bit1 x) XOR numeral (Num.Bit0 y) = (numeral x XOR numeral y) BIT True"
  "numeral (Num.Bit1 x) XOR numeral (Num.Bit1 y) = (numeral x XOR numeral y) BIT False"
  "numeral (Num.Bit0 x) XOR - numeral (Num.Bit0 y) = (numeral x XOR - numeral y) BIT False"
  "numeral (Num.Bit0 x) XOR - numeral (Num.Bit1 y) = (numeral x XOR - numeral (y + Num.One)) BIT True"
  "numeral (Num.Bit1 x) XOR - numeral (Num.Bit0 y) = (numeral x XOR - numeral y) BIT True"
  "numeral (Num.Bit1 x) XOR - numeral (Num.Bit1 y) = (numeral x XOR - numeral (y + Num.One)) BIT False"
  "- numeral (Num.Bit0 x) XOR numeral (Num.Bit0 y) = (- numeral x XOR numeral y) BIT False"
  "- numeral (Num.Bit0 x) XOR numeral (Num.Bit1 y) = (- numeral x XOR numeral y) BIT True"
  "- numeral (Num.Bit1 x) XOR numeral (Num.Bit0 y) = (- numeral (x + Num.One) XOR numeral y) BIT True"
  "- numeral (Num.Bit1 x) XOR numeral (Num.Bit1 y) = (- numeral (x + Num.One) XOR numeral y) BIT False"
  "- numeral (Num.Bit0 x) XOR - numeral (Num.Bit0 y) = (- numeral x XOR - numeral y) BIT False"
  "- numeral (Num.Bit0 x) XOR - numeral (Num.Bit1 y) = (- numeral x XOR - numeral (y + Num.One)) BIT True"
  "- numeral (Num.Bit1 x) XOR - numeral (Num.Bit0 y) = (- numeral (x + Num.One) XOR - numeral y) BIT True"
  "- numeral (Num.Bit1 x) XOR - numeral (Num.Bit1 y) = (- numeral (x + Num.One) XOR - numeral (y + Num.One)) BIT False"
  "(1::int) XOR numeral (Num.Bit0 y) = numeral (Num.Bit1 y)"
  "(1::int) XOR numeral (Num.Bit1 y) = numeral (Num.Bit0 y)"
  "(1::int) XOR - numeral (Num.Bit0 y) = - numeral (Num.BitM y)"
  "(1::int) XOR - numeral (Num.Bit1 y) = - numeral (Num.Bit0 (y + Num.One))"
  "numeral (Num.Bit0 x) XOR (1::int) = numeral (Num.Bit1 x)"
  "numeral (Num.Bit1 x) XOR (1::int) = numeral (Num.Bit0 x)"
  "- numeral (Num.Bit0 x) XOR (1::int) = - numeral (Num.BitM x)"
  "- numeral (Num.Bit1 x) XOR (1::int) = - numeral (Num.Bit0 (x + Num.One))"
  by (rule bin_rl_eqI; simp)+


subsubsection \<open>Interactions with arithmetic\<close>

lemma plus_and_or [rule_format]: "\<forall>y::int. (x AND y) + (x OR y) = x + y"
  apply (induct x rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (case_tac y rule: bin_exhaust)
  apply clarsimp
  apply (unfold Bit_def)
  apply clarsimp
  apply (erule_tac x = "x" in allE)
  apply simp
  done

lemma le_int_or: "bin_sign y = 0 \<Longrightarrow> x \<le> x OR y"
  for x y :: int
  apply (induct y arbitrary: x rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply (case_tac x rule: bin_exhaust)
  apply (case_tac b)
   apply (case_tac [!] bit)
     apply (auto simp: le_Bits)
  done

lemmas int_and_le =
  xtrans(3) [OF bbw_ao_absorbs (2) [THEN conjunct2, symmetric] le_int_or]

text \<open>Interaction between bit-wise and arithmetic: good example of \<open>bin_induction\<close>.\<close>
lemma bin_add_not: "x + NOT x = (-1::int)"
  apply (induct x rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply (case_tac bit, auto)
  done

lemma mod_BIT: "bin BIT bit mod 2 ^ Suc n = (bin mod 2 ^ n) BIT bit"
proof -
  have "2 * (bin mod 2 ^ n) + 1 = (2 * bin mod 2 ^ Suc n) + 1"
    by (simp add: mod_mult_mult1)
  also have "\<dots> = ((2 * bin mod 2 ^ Suc n) + 1) mod 2 ^ Suc n"
    by (simp add: ac_simps pos_zmod_mult_2)
  also have "\<dots> = (2 * bin + 1) mod 2 ^ Suc n"
    by (simp only: mod_simps)
  finally show ?thesis
    by (auto simp add: Bit_def)
qed

lemma AND_mod: "x AND 2 ^ n - 1 = x mod 2 ^ n"
  for x :: int
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
    then show ?thesis by simp
  next
    case (Suc m)
    with 3 show ?thesis
      by (simp only: power_BIT mod_BIT int_and_Bits) simp
  qed
qed


subsubsection \<open>Comparison\<close>

lemma AND_lower [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> x"
  shows "0 \<le> x AND y"
  using assms
proof (induct x arbitrary: y rule: bin_induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by (simp only: Min_def)
next
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
qed

lemma OR_lower [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
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

lemma XOR_lower [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
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

lemma AND_upper1 [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
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

lemmas AND_upper1' [simp] = order_trans [OF AND_upper1] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
lemmas AND_upper1'' [simp] = order_le_less_trans [OF AND_upper1] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>

lemma AND_upper2 [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> y"
  shows "x AND y \<le> y"
  using assms
proof (induct y arbitrary: x rule: bin_induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by (simp only: Min_def)
next
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
qed

lemmas AND_upper2' [simp] = order_trans [OF AND_upper2] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
lemmas AND_upper2'' [simp] = order_le_less_trans [OF AND_upper2] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>

lemma OR_upper: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
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
      then show ?thesis using 0 1 \<open>y < 2 ^ n\<close>
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

lemma XOR_upper: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> x" "x < 2 ^ n" "y < 2 ^ n"
  shows "x XOR y < 2 ^ n"
  using assms
proof (induct x arbitrary: y n rule: bin_induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by (simp only: Min_def)
next
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
      then show ?thesis using 0 1 \<open>y < 2 ^ n\<close>
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
qed



subsubsection \<open>Truncating results of bit-wise operations\<close>

lemma bin_trunc_ao:
  "bintrunc n x AND bintrunc n y = bintrunc n (x AND y)"
  "bintrunc n x OR bintrunc n y = bintrunc n (x OR y)"
  by (auto simp add: bin_eq_iff bin_nth_ops nth_bintr)

lemma bin_trunc_xor: "bintrunc n (bintrunc n x XOR bintrunc n y) = bintrunc n (x XOR y)"
  by (auto simp add: bin_eq_iff bin_nth_ops nth_bintr)

lemma bin_trunc_not: "bintrunc n (NOT (bintrunc n x)) = bintrunc n (NOT x)"
  by (auto simp add: bin_eq_iff bin_nth_ops nth_bintr)

text \<open>Want theorems of the form of \<open>bin_trunc_xor\<close>.\<close>
lemma bintr_bintr_i: "x = bintrunc n y \<Longrightarrow> bintrunc n x = bintrunc n y"
  by auto

lemmas bin_trunc_and = bin_trunc_ao(1) [THEN bintr_bintr_i]
lemmas bin_trunc_or = bin_trunc_ao(2) [THEN bintr_bintr_i]

lemma bl_xor_aux_bin:
  "map2 (\<lambda>x y. x \<noteq> y) (bin_to_bl_aux n v bs) (bin_to_bl_aux n w cs) =
    bin_to_bl_aux n (v XOR w) (map2 (\<lambda>x y. x \<noteq> y) bs cs)"
  apply (induct n arbitrary: v w bs cs)
   apply simp
  apply (case_tac v rule: bin_exhaust)
  apply (case_tac w rule: bin_exhaust)
  apply clarsimp
  apply (case_tac b)
   apply auto
  done

lemma bl_or_aux_bin:
  "map2 (\<or>) (bin_to_bl_aux n v bs) (bin_to_bl_aux n w cs) =
    bin_to_bl_aux n (v OR w) (map2 (\<or>) bs cs)"
  apply (induct n arbitrary: v w bs cs)
   apply simp
  apply (case_tac v rule: bin_exhaust)
  apply (case_tac w rule: bin_exhaust)
  apply clarsimp
  done

lemma bl_and_aux_bin:
  "map2 (\<and>) (bin_to_bl_aux n v bs) (bin_to_bl_aux n w cs) =
    bin_to_bl_aux n (v AND w) (map2 (\<and>) bs cs)"
  apply (induct n arbitrary: v w bs cs)
   apply simp
  apply (case_tac v rule: bin_exhaust)
  apply (case_tac w rule: bin_exhaust)
  apply clarsimp
  done

lemma bl_not_aux_bin: "map Not (bin_to_bl_aux n w cs) = bin_to_bl_aux n (NOT w) (map Not cs)"
  by (induct n arbitrary: w cs) auto

lemma bl_not_bin: "map Not (bin_to_bl n w) = bin_to_bl n (NOT w)"
  by (simp add: bin_to_bl_def bl_not_aux_bin)

lemma bl_and_bin: "map2 (\<and>) (bin_to_bl n v) (bin_to_bl n w) = bin_to_bl n (v AND w)"
  by (simp add: bin_to_bl_def bl_and_aux_bin)

lemma bl_or_bin: "map2 (\<or>) (bin_to_bl n v) (bin_to_bl n w) = bin_to_bl n (v OR w)"
  by (simp add: bin_to_bl_def bl_or_aux_bin)

lemma bl_xor_bin: "map2 (\<lambda>x y. x \<noteq> y) (bin_to_bl n v) (bin_to_bl n w) = bin_to_bl n (v XOR w)"
  by (simp only: bin_to_bl_def bl_xor_aux_bin map2_Nil)


subsection \<open>Setting and clearing bits\<close>

text \<open>nth bit, set/clear\<close>

primrec bin_sc :: "nat \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> int"
  where
    Z: "bin_sc 0 b w = bin_rest w BIT b"
  | Suc: "bin_sc (Suc n) b w = bin_sc n b (bin_rest w) BIT bin_last w"

lemma bin_nth_sc [simp]: "bin_nth (bin_sc n b w) n \<longleftrightarrow> b"
  by (induct n arbitrary: w) auto

lemma bin_sc_sc_same [simp]: "bin_sc n c (bin_sc n b w) = bin_sc n c w"
  by (induct n arbitrary: w) auto

lemma bin_sc_sc_diff: "m \<noteq> n \<Longrightarrow> bin_sc m c (bin_sc n b w) = bin_sc n b (bin_sc m c w)"
  apply (induct n arbitrary: w m)
   apply (case_tac [!] m)
     apply auto
  done

lemma bin_nth_sc_gen: "bin_nth (bin_sc n b w) m = (if m = n then b else bin_nth w m)"
  by (induct n arbitrary: w m) (case_tac [!] m, auto)

lemma bin_sc_nth [simp]: "bin_sc n (bin_nth w n) w = w"
  by (induct n arbitrary: w) auto

lemma bin_sign_sc [simp]: "bin_sign (bin_sc n b w) = bin_sign w"
  by (induct n arbitrary: w) auto

lemma bin_sc_bintr [simp]: "bintrunc m (bin_sc n x (bintrunc m (w))) = bintrunc m (bin_sc n x w)"
  apply (induct n arbitrary: w m)
   apply (case_tac [!] w rule: bin_exhaust)
   apply (case_tac [!] m, auto)
  done

lemma bin_clr_le: "bin_sc n False w \<le> w"
  apply (induct n arbitrary: w)
   apply (case_tac [!] w rule: bin_exhaust)
   apply (auto simp: le_Bits)
  done

lemma bin_set_ge: "bin_sc n True w \<ge> w"
  apply (induct n arbitrary: w)
   apply (case_tac [!] w rule: bin_exhaust)
   apply (auto simp: le_Bits)
  done

lemma bintr_bin_clr_le: "bintrunc n (bin_sc m False w) \<le> bintrunc n w"
  apply (induct n arbitrary: w m)
   apply simp
  apply (case_tac w rule: bin_exhaust)
  apply (case_tac m)
   apply (auto simp: le_Bits)
  done

lemma bintr_bin_set_ge: "bintrunc n (bin_sc m True w) \<ge> bintrunc n w"
  apply (induct n arbitrary: w m)
   apply simp
  apply (case_tac w rule: bin_exhaust)
  apply (case_tac m)
   apply (auto simp: le_Bits)
  done

lemma bin_sc_FP [simp]: "bin_sc n False 0 = 0"
  by (induct n) auto

lemma bin_sc_TM [simp]: "bin_sc n True (- 1) = - 1"
  by (induct n) auto

lemmas bin_sc_simps = bin_sc.Z bin_sc.Suc bin_sc_TM bin_sc_FP

lemma bin_sc_minus: "0 < n \<Longrightarrow> bin_sc (Suc (n - 1)) b w = bin_sc n b w"
  by auto

lemmas bin_sc_Suc_minus =
  trans [OF bin_sc_minus [symmetric] bin_sc.Suc]

lemma bin_sc_numeral [simp]:
  "bin_sc (numeral k) b w =
    bin_sc (pred_numeral k) b (bin_rest w) BIT bin_last w"
  by (simp add: numeral_eq_Suc)

instantiation int :: bitss
begin

definition [iff]: "i !! n \<longleftrightarrow> bin_nth i n"

definition "lsb i = i !! 0" for i :: int

definition "set_bit i n b = bin_sc n b i"

definition
  "set_bits f =
    (if \<exists>n. \<forall>n'\<ge>n. \<not> f n' then
      let n = LEAST n. \<forall>n'\<ge>n. \<not> f n'
      in bl_to_bin (rev (map f [0..<n]))
     else if \<exists>n. \<forall>n'\<ge>n. f n' then
      let n = LEAST n. \<forall>n'\<ge>n. f n'
      in sbintrunc n (bl_to_bin (True # rev (map f [0..<n])))
     else 0 :: int)"

definition "shiftl x n = x * 2 ^ n" for x :: int

definition "shiftr x n = x div 2 ^ n" for x :: int

definition "msb x \<longleftrightarrow> x < 0" for x :: int

instance ..

end

end
