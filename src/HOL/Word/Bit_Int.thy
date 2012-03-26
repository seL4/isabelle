(* 
  Author: Jeremy Dawson and Gerwin Klein, NICTA

  Definitions and basic theorems for bit-wise logical operations 
  for integers expressed using Pls, Min, BIT,
  and converting them to and from lists of bools.
*) 

header {* Bitwise Operations on Binary Integers *}

theory Bit_Int
imports Bit_Representation Bit_Operations
begin

subsection {* Logical operations *}

text "bit-wise logical operations on the int type"

instantiation int :: bit
begin

definition int_not_def:
  "bitNOT = (\<lambda>x::int. - x - 1)"

function bitAND_int where
  "bitAND_int x y =
    (if x = 0 then 0 else if x = -1 then y else
      (bin_rest x AND bin_rest y) BIT (bin_last x AND bin_last y))"
  by pat_completeness simp

termination
  by (relation "measure (nat o abs o fst)", simp_all add: bin_rest_def)

declare bitAND_int.simps [simp del]

definition int_or_def:
  "bitOR = (\<lambda>x y::int. NOT (NOT x AND NOT y))"

definition int_xor_def:
  "bitXOR = (\<lambda>x y::int. (x AND NOT y) OR (NOT x AND y))"

instance ..

end

subsubsection {* Basic simplification rules *}

lemma int_not_BIT [simp]:
  "NOT (w BIT b) = (NOT w) BIT (NOT b)"
  unfolding int_not_def Bit_def by (cases b, simp_all)

lemma int_not_simps [simp]:
  "NOT (0::int) = -1"
  "NOT (1::int) = -2"
  "NOT (-1::int) = 0"
  "NOT (numeral w::int) = neg_numeral (w + Num.One)"
  "NOT (neg_numeral (Num.Bit0 w)::int) = numeral (Num.BitM w)"
  "NOT (neg_numeral (Num.Bit1 w)::int) = numeral (Num.Bit0 w)"
  unfolding int_not_def by simp_all

lemma int_not_not [simp]: "NOT (NOT (x::int)) = x"
  unfolding int_not_def by simp

lemma int_and_0 [simp]: "(0::int) AND x = 0"
  by (simp add: bitAND_int.simps)

lemma int_and_m1 [simp]: "(-1::int) AND x = x"
  by (simp add: bitAND_int.simps)

lemma Bit_eq_0_iff: "w BIT b = 0 \<longleftrightarrow> w = 0 \<and> b = 0"
  by (subst BIT_eq_iff [symmetric], simp)

lemma Bit_eq_m1_iff: "w BIT b = -1 \<longleftrightarrow> w = -1 \<and> b = 1"
  by (subst BIT_eq_iff [symmetric], simp)

lemma int_and_Bits [simp]: 
  "(x BIT b) AND (y BIT c) = (x AND y) BIT (b AND c)" 
  by (subst bitAND_int.simps, simp add: Bit_eq_0_iff Bit_eq_m1_iff)

lemma int_or_zero [simp]: "(0::int) OR x = x"
  unfolding int_or_def by simp

lemma int_or_minus1 [simp]: "(-1::int) OR x = -1"
  unfolding int_or_def by simp

lemma bit_or_def: "(b::bit) OR c = NOT (NOT b AND NOT c)"
  by (induct b, simp_all) (* TODO: move *)

lemma int_or_Bits [simp]: 
  "(x BIT b) OR (y BIT c) = (x OR y) BIT (b OR c)"
  unfolding int_or_def bit_or_def by simp

lemma int_xor_zero [simp]: "(0::int) XOR x = x"
  unfolding int_xor_def by simp

lemma bit_xor_def: "(b::bit) XOR c = (b AND NOT c) OR (NOT b AND c)"
  by (induct b, simp_all) (* TODO: move *)

lemma int_xor_Bits [simp]: 
  "(x BIT b) XOR (y BIT c) = (x XOR y) BIT (b XOR c)"
  unfolding int_xor_def bit_xor_def by simp

subsubsection {* Binary destructors *}

lemma bin_rest_NOT [simp]: "bin_rest (NOT x) = NOT (bin_rest x)"
  by (cases x rule: bin_exhaust, simp)

lemma bin_last_NOT [simp]: "bin_last (NOT x) = NOT (bin_last x)"
  by (cases x rule: bin_exhaust, simp)

lemma bin_rest_AND [simp]: "bin_rest (x AND y) = bin_rest x AND bin_rest y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust, simp)

lemma bin_last_AND [simp]: "bin_last (x AND y) = bin_last x AND bin_last y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust, simp)

lemma bin_rest_OR [simp]: "bin_rest (x OR y) = bin_rest x OR bin_rest y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust, simp)

lemma bin_last_OR [simp]: "bin_last (x OR y) = bin_last x OR bin_last y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust, simp)

lemma bin_rest_XOR [simp]: "bin_rest (x XOR y) = bin_rest x XOR bin_rest y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust, simp)

lemma bin_last_XOR [simp]: "bin_last (x XOR y) = bin_last x XOR bin_last y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust, simp)

lemma bit_NOT_eq_1_iff [simp]: "NOT (b::bit) = 1 \<longleftrightarrow> b = 0"
  by (induct b, simp_all)

lemma bit_AND_eq_1_iff [simp]: "(a::bit) AND b = 1 \<longleftrightarrow> a = 1 \<and> b = 1"
  by (induct a, simp_all)

lemma bin_nth_ops:
  "!!x y. bin_nth (x AND y) n = (bin_nth x n & bin_nth y n)" 
  "!!x y. bin_nth (x OR y) n = (bin_nth x n | bin_nth y n)"
  "!!x y. bin_nth (x XOR y) n = (bin_nth x n ~= bin_nth y n)" 
  "!!x. bin_nth (NOT x) n = (~ bin_nth x n)"
  by (induct n) auto

subsubsection {* Derived properties *}

lemma int_xor_minus1 [simp]: "(-1::int) XOR x = NOT x"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_xor_extra_simps [simp]:
  "w XOR (0::int) = w"
  "w XOR (-1::int) = NOT w"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_or_extra_simps [simp]:
  "w OR (0::int) = w"
  "w OR (-1::int) = -1"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_and_extra_simps [simp]:
  "w AND (0::int) = 0"
  "w AND (-1::int) = w"
  by (auto simp add: bin_eq_iff bin_nth_ops)

(* commutativity of the above *)
lemma bin_ops_comm:
  shows
  int_and_comm: "!!y::int. x AND y = y AND x" and
  int_or_comm:  "!!y::int. x OR y = y OR x" and
  int_xor_comm: "!!y::int. x XOR y = y XOR x"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bin_ops_same [simp]:
  "(x::int) AND x = x" 
  "(x::int) OR x = x" 
  "(x::int) XOR x = 0"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemmas bin_log_esimps = 
  int_and_extra_simps  int_or_extra_simps  int_xor_extra_simps
  int_and_0 int_and_m1 int_or_zero int_or_minus1 int_xor_zero int_xor_minus1

(* basic properties of logical (bit-wise) operations *)

lemma bbw_ao_absorb: 
  "!!y::int. x AND (y OR x) = x & x OR (y AND x) = x"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_ao_absorbs_other:
  "x AND (x OR y) = x \<and> (y AND x) OR x = (x::int)"
  "(y OR x) AND x = x \<and> x OR (x AND y) = (x::int)"
  "(x OR y) AND x = x \<and> (x AND y) OR x = (x::int)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemmas bbw_ao_absorbs [simp] = bbw_ao_absorb bbw_ao_absorbs_other

lemma int_xor_not:
  "!!y::int. (NOT x) XOR y = NOT (x XOR y) & 
        x XOR (NOT y) = NOT (x XOR y)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_and_assoc:
  "(x AND y) AND (z::int) = x AND (y AND z)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_or_assoc:
  "(x OR y) OR (z::int) = x OR (y OR z)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_xor_assoc:
  "(x XOR y) XOR (z::int) = x XOR (y XOR z)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemmas bbw_assocs = int_and_assoc int_or_assoc int_xor_assoc

(* BH: Why are these declared as simp rules??? *)
lemma bbw_lcs [simp]: 
  "(y::int) AND (x AND z) = x AND (y AND z)"
  "(y::int) OR (x OR z) = x OR (y OR z)"
  "(y::int) XOR (x XOR z) = x XOR (y XOR z)" 
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_not_dist: 
  "!!y::int. NOT (x OR y) = (NOT x) AND (NOT y)" 
  "!!y::int. NOT (x AND y) = (NOT x) OR (NOT y)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_oa_dist: 
  "!!y z::int. (x AND y) OR z = 
          (x OR z) AND (y OR z)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_ao_dist: 
  "!!y z::int. (x OR y) AND z = 
          (x AND z) OR (y AND z)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

(*
Why were these declared simp???
declare bin_ops_comm [simp] bbw_assocs [simp] 
*)

subsubsection {* Simplification with numerals *}

text {* Cases for @{text "0"} and @{text "-1"} are already covered by
  other simp rules. *}

lemma bin_rl_eqI: "\<lbrakk>bin_rest x = bin_rest y; bin_last x = bin_last y\<rbrakk> \<Longrightarrow> x = y"
  by (metis bin_rl_simp)

lemma bin_rest_neg_numeral_BitM [simp]:
  "bin_rest (neg_numeral (Num.BitM w)) = neg_numeral w"
  by (simp only: BIT_bin_simps [symmetric] bin_rest_BIT)

lemma bin_last_neg_numeral_BitM [simp]:
  "bin_last (neg_numeral (Num.BitM w)) = 1"
  by (simp only: BIT_bin_simps [symmetric] bin_last_BIT)

text {* FIXME: The rule sets below are very large (24 rules for each
  operator). Is there a simpler way to do this? *}

lemma int_and_numerals [simp]:
  "numeral (Num.Bit0 x) AND numeral (Num.Bit0 y) = (numeral x AND numeral y) BIT 0"
  "numeral (Num.Bit0 x) AND numeral (Num.Bit1 y) = (numeral x AND numeral y) BIT 0"
  "numeral (Num.Bit1 x) AND numeral (Num.Bit0 y) = (numeral x AND numeral y) BIT 0"
  "numeral (Num.Bit1 x) AND numeral (Num.Bit1 y) = (numeral x AND numeral y) BIT 1"
  "numeral (Num.Bit0 x) AND neg_numeral (Num.Bit0 y) = (numeral x AND neg_numeral y) BIT 0"
  "numeral (Num.Bit0 x) AND neg_numeral (Num.Bit1 y) = (numeral x AND neg_numeral (y + Num.One)) BIT 0"
  "numeral (Num.Bit1 x) AND neg_numeral (Num.Bit0 y) = (numeral x AND neg_numeral y) BIT 0"
  "numeral (Num.Bit1 x) AND neg_numeral (Num.Bit1 y) = (numeral x AND neg_numeral (y + Num.One)) BIT 1"
  "neg_numeral (Num.Bit0 x) AND numeral (Num.Bit0 y) = (neg_numeral x AND numeral y) BIT 0"
  "neg_numeral (Num.Bit0 x) AND numeral (Num.Bit1 y) = (neg_numeral x AND numeral y) BIT 0"
  "neg_numeral (Num.Bit1 x) AND numeral (Num.Bit0 y) = (neg_numeral (x + Num.One) AND numeral y) BIT 0"
  "neg_numeral (Num.Bit1 x) AND numeral (Num.Bit1 y) = (neg_numeral (x + Num.One) AND numeral y) BIT 1"
  "neg_numeral (Num.Bit0 x) AND neg_numeral (Num.Bit0 y) = (neg_numeral x AND neg_numeral y) BIT 0"
  "neg_numeral (Num.Bit0 x) AND neg_numeral (Num.Bit1 y) = (neg_numeral x AND neg_numeral (y + Num.One)) BIT 0"
  "neg_numeral (Num.Bit1 x) AND neg_numeral (Num.Bit0 y) = (neg_numeral (x + Num.One) AND neg_numeral y) BIT 0"
  "neg_numeral (Num.Bit1 x) AND neg_numeral (Num.Bit1 y) = (neg_numeral (x + Num.One) AND neg_numeral (y + Num.One)) BIT 1"
  "(1::int) AND numeral (Num.Bit0 y) = 0"
  "(1::int) AND numeral (Num.Bit1 y) = 1"
  "(1::int) AND neg_numeral (Num.Bit0 y) = 0"
  "(1::int) AND neg_numeral (Num.Bit1 y) = 1"
  "numeral (Num.Bit0 x) AND (1::int) = 0"
  "numeral (Num.Bit1 x) AND (1::int) = 1"
  "neg_numeral (Num.Bit0 x) AND (1::int) = 0"
  "neg_numeral (Num.Bit1 x) AND (1::int) = 1"
  by (rule bin_rl_eqI, simp, simp)+

lemma int_or_numerals [simp]:
  "numeral (Num.Bit0 x) OR numeral (Num.Bit0 y) = (numeral x OR numeral y) BIT 0"
  "numeral (Num.Bit0 x) OR numeral (Num.Bit1 y) = (numeral x OR numeral y) BIT 1"
  "numeral (Num.Bit1 x) OR numeral (Num.Bit0 y) = (numeral x OR numeral y) BIT 1"
  "numeral (Num.Bit1 x) OR numeral (Num.Bit1 y) = (numeral x OR numeral y) BIT 1"
  "numeral (Num.Bit0 x) OR neg_numeral (Num.Bit0 y) = (numeral x OR neg_numeral y) BIT 0"
  "numeral (Num.Bit0 x) OR neg_numeral (Num.Bit1 y) = (numeral x OR neg_numeral (y + Num.One)) BIT 1"
  "numeral (Num.Bit1 x) OR neg_numeral (Num.Bit0 y) = (numeral x OR neg_numeral y) BIT 1"
  "numeral (Num.Bit1 x) OR neg_numeral (Num.Bit1 y) = (numeral x OR neg_numeral (y + Num.One)) BIT 1"
  "neg_numeral (Num.Bit0 x) OR numeral (Num.Bit0 y) = (neg_numeral x OR numeral y) BIT 0"
  "neg_numeral (Num.Bit0 x) OR numeral (Num.Bit1 y) = (neg_numeral x OR numeral y) BIT 1"
  "neg_numeral (Num.Bit1 x) OR numeral (Num.Bit0 y) = (neg_numeral (x + Num.One) OR numeral y) BIT 1"
  "neg_numeral (Num.Bit1 x) OR numeral (Num.Bit1 y) = (neg_numeral (x + Num.One) OR numeral y) BIT 1"
  "neg_numeral (Num.Bit0 x) OR neg_numeral (Num.Bit0 y) = (neg_numeral x OR neg_numeral y) BIT 0"
  "neg_numeral (Num.Bit0 x) OR neg_numeral (Num.Bit1 y) = (neg_numeral x OR neg_numeral (y + Num.One)) BIT 1"
  "neg_numeral (Num.Bit1 x) OR neg_numeral (Num.Bit0 y) = (neg_numeral (x + Num.One) OR neg_numeral y) BIT 1"
  "neg_numeral (Num.Bit1 x) OR neg_numeral (Num.Bit1 y) = (neg_numeral (x + Num.One) OR neg_numeral (y + Num.One)) BIT 1"
  "(1::int) OR numeral (Num.Bit0 y) = numeral (Num.Bit1 y)"
  "(1::int) OR numeral (Num.Bit1 y) = numeral (Num.Bit1 y)"
  "(1::int) OR neg_numeral (Num.Bit0 y) = neg_numeral (Num.BitM y)"
  "(1::int) OR neg_numeral (Num.Bit1 y) = neg_numeral (Num.Bit1 y)"
  "numeral (Num.Bit0 x) OR (1::int) = numeral (Num.Bit1 x)"
  "numeral (Num.Bit1 x) OR (1::int) = numeral (Num.Bit1 x)"
  "neg_numeral (Num.Bit0 x) OR (1::int) = neg_numeral (Num.BitM x)"
  "neg_numeral (Num.Bit1 x) OR (1::int) = neg_numeral (Num.Bit1 x)"
  by (rule bin_rl_eqI, simp, simp)+

lemma int_xor_numerals [simp]:
  "numeral (Num.Bit0 x) XOR numeral (Num.Bit0 y) = (numeral x XOR numeral y) BIT 0"
  "numeral (Num.Bit0 x) XOR numeral (Num.Bit1 y) = (numeral x XOR numeral y) BIT 1"
  "numeral (Num.Bit1 x) XOR numeral (Num.Bit0 y) = (numeral x XOR numeral y) BIT 1"
  "numeral (Num.Bit1 x) XOR numeral (Num.Bit1 y) = (numeral x XOR numeral y) BIT 0"
  "numeral (Num.Bit0 x) XOR neg_numeral (Num.Bit0 y) = (numeral x XOR neg_numeral y) BIT 0"
  "numeral (Num.Bit0 x) XOR neg_numeral (Num.Bit1 y) = (numeral x XOR neg_numeral (y + Num.One)) BIT 1"
  "numeral (Num.Bit1 x) XOR neg_numeral (Num.Bit0 y) = (numeral x XOR neg_numeral y) BIT 1"
  "numeral (Num.Bit1 x) XOR neg_numeral (Num.Bit1 y) = (numeral x XOR neg_numeral (y + Num.One)) BIT 0"
  "neg_numeral (Num.Bit0 x) XOR numeral (Num.Bit0 y) = (neg_numeral x XOR numeral y) BIT 0"
  "neg_numeral (Num.Bit0 x) XOR numeral (Num.Bit1 y) = (neg_numeral x XOR numeral y) BIT 1"
  "neg_numeral (Num.Bit1 x) XOR numeral (Num.Bit0 y) = (neg_numeral (x + Num.One) XOR numeral y) BIT 1"
  "neg_numeral (Num.Bit1 x) XOR numeral (Num.Bit1 y) = (neg_numeral (x + Num.One) XOR numeral y) BIT 0"
  "neg_numeral (Num.Bit0 x) XOR neg_numeral (Num.Bit0 y) = (neg_numeral x XOR neg_numeral y) BIT 0"
  "neg_numeral (Num.Bit0 x) XOR neg_numeral (Num.Bit1 y) = (neg_numeral x XOR neg_numeral (y + Num.One)) BIT 1"
  "neg_numeral (Num.Bit1 x) XOR neg_numeral (Num.Bit0 y) = (neg_numeral (x + Num.One) XOR neg_numeral y) BIT 1"
  "neg_numeral (Num.Bit1 x) XOR neg_numeral (Num.Bit1 y) = (neg_numeral (x + Num.One) XOR neg_numeral (y + Num.One)) BIT 0"
  "(1::int) XOR numeral (Num.Bit0 y) = numeral (Num.Bit1 y)"
  "(1::int) XOR numeral (Num.Bit1 y) = numeral (Num.Bit0 y)"
  "(1::int) XOR neg_numeral (Num.Bit0 y) = neg_numeral (Num.BitM y)"
  "(1::int) XOR neg_numeral (Num.Bit1 y) = neg_numeral (Num.Bit0 (y + Num.One))"
  "numeral (Num.Bit0 x) XOR (1::int) = numeral (Num.Bit1 x)"
  "numeral (Num.Bit1 x) XOR (1::int) = numeral (Num.Bit0 x)"
  "neg_numeral (Num.Bit0 x) XOR (1::int) = neg_numeral (Num.BitM x)"
  "neg_numeral (Num.Bit1 x) XOR (1::int) = neg_numeral (Num.Bit0 (x + Num.One))"
  by (rule bin_rl_eqI, simp, simp)+

subsubsection {* Interactions with arithmetic *}

lemma plus_and_or [rule_format]:
  "ALL y::int. (x AND y) + (x OR y) = x + y"
  apply (induct x rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (case_tac y rule: bin_exhaust)
  apply clarsimp
  apply (unfold Bit_def)
  apply clarsimp
  apply (erule_tac x = "x" in allE)
  apply (simp add: bitval_def split: bit.split)
  done

lemma le_int_or:
  "bin_sign (y::int) = 0 ==> x <= x OR y"
  apply (induct y arbitrary: x rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply (case_tac x rule: bin_exhaust)
  apply (case_tac b)
   apply (case_tac [!] bit)
     apply (auto simp: le_Bits)
  done

lemmas int_and_le =
  xtr3 [OF bbw_ao_absorbs (2) [THEN conjunct2, symmetric] le_int_or]

lemma add_BIT_simps [simp]: (* FIXME: move *)
  "x BIT 0 + y BIT 0 = (x + y) BIT 0"
  "x BIT 0 + y BIT 1 = (x + y) BIT 1"
  "x BIT 1 + y BIT 0 = (x + y) BIT 1"
  "x BIT 1 + y BIT 1 = (x + y + 1) BIT 0"
  by (simp_all add: Bit_B0_2t Bit_B1_2t)

(* interaction between bit-wise and arithmetic *)
(* good example of bin_induction *)
lemma bin_add_not: "x + NOT x = (-1::int)"
  apply (induct x rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply (case_tac bit, auto)
  done

subsubsection {* Truncating results of bit-wise operations *}

lemma bin_trunc_ao: 
  "!!x y. (bintrunc n x) AND (bintrunc n y) = bintrunc n (x AND y)" 
  "!!x y. (bintrunc n x) OR (bintrunc n y) = bintrunc n (x OR y)"
  by (auto simp add: bin_eq_iff bin_nth_ops nth_bintr)

lemma bin_trunc_xor: 
  "!!x y. bintrunc n (bintrunc n x XOR bintrunc n y) = 
          bintrunc n (x XOR y)"
  by (auto simp add: bin_eq_iff bin_nth_ops nth_bintr)

lemma bin_trunc_not: 
  "!!x. bintrunc n (NOT (bintrunc n x)) = bintrunc n (NOT x)"
  by (auto simp add: bin_eq_iff bin_nth_ops nth_bintr)

(* want theorems of the form of bin_trunc_xor *)
lemma bintr_bintr_i:
  "x = bintrunc n y ==> bintrunc n x = bintrunc n y"
  by auto

lemmas bin_trunc_and = bin_trunc_ao(1) [THEN bintr_bintr_i]
lemmas bin_trunc_or = bin_trunc_ao(2) [THEN bintr_bintr_i]

subsection {* Setting and clearing bits *}

primrec
  bin_sc :: "nat => bit => int => int"
where
  Z: "bin_sc 0 b w = bin_rest w BIT b"
  | Suc: "bin_sc (Suc n) b w = bin_sc n b (bin_rest w) BIT bin_last w"

(** nth bit, set/clear **)

lemma bin_nth_sc [simp]: 
  "bin_nth (bin_sc n b w) n = (b = 1)"
  by (induct n arbitrary: w) auto

lemma bin_sc_sc_same [simp]: 
  "bin_sc n c (bin_sc n b w) = bin_sc n c w"
  by (induct n arbitrary: w) auto

lemma bin_sc_sc_diff:
  "m ~= n ==> 
    bin_sc m c (bin_sc n b w) = bin_sc n b (bin_sc m c w)"
  apply (induct n arbitrary: w m)
   apply (case_tac [!] m)
     apply auto
  done

lemma bin_nth_sc_gen: 
  "bin_nth (bin_sc n b w) m = (if m = n then b = 1 else bin_nth w m)"
  by (induct n arbitrary: w m) (case_tac [!] m, auto)
  
lemma bin_sc_nth [simp]:
  "(bin_sc n (If (bin_nth w n) 1 0) w) = w"
  by (induct n arbitrary: w) auto

lemma bin_sign_sc [simp]:
  "bin_sign (bin_sc n b w) = bin_sign w"
  by (induct n arbitrary: w) auto
  
lemma bin_sc_bintr [simp]: 
  "bintrunc m (bin_sc n x (bintrunc m (w))) = bintrunc m (bin_sc n x w)"
  apply (induct n arbitrary: w m)
   apply (case_tac [!] w rule: bin_exhaust)
   apply (case_tac [!] m, auto)
  done

lemma bin_clr_le:
  "bin_sc n 0 w <= w"
  apply (induct n arbitrary: w)
   apply (case_tac [!] w rule: bin_exhaust)
   apply (auto simp: le_Bits)
  done

lemma bin_set_ge:
  "bin_sc n 1 w >= w"
  apply (induct n arbitrary: w)
   apply (case_tac [!] w rule: bin_exhaust)
   apply (auto simp: le_Bits)
  done

lemma bintr_bin_clr_le:
  "bintrunc n (bin_sc m 0 w) <= bintrunc n w"
  apply (induct n arbitrary: w m)
   apply simp
  apply (case_tac w rule: bin_exhaust)
  apply (case_tac m)
   apply (auto simp: le_Bits)
  done

lemma bintr_bin_set_ge:
  "bintrunc n (bin_sc m 1 w) >= bintrunc n w"
  apply (induct n arbitrary: w m)
   apply simp
  apply (case_tac w rule: bin_exhaust)
  apply (case_tac m)
   apply (auto simp: le_Bits)
  done

lemma bin_sc_FP [simp]: "bin_sc n 0 0 = 0"
  by (induct n) auto

lemma bin_sc_TM [simp]: "bin_sc n 1 -1 = -1"
  by (induct n) auto
  
lemmas bin_sc_simps = bin_sc.Z bin_sc.Suc bin_sc_TM bin_sc_FP

lemma bin_sc_minus:
  "0 < n ==> bin_sc (Suc (n - 1)) b w = bin_sc n b w"
  by auto

lemmas bin_sc_Suc_minus = 
  trans [OF bin_sc_minus [symmetric] bin_sc.Suc]

lemma bin_sc_numeral [simp]:
  "bin_sc (numeral k) b w =
    bin_sc (numeral k - 1) b (bin_rest w) BIT bin_last w"
  by (subst expand_Suc, rule bin_sc.Suc)


subsection {* Splitting and concatenation *}

definition bin_rcat :: "nat \<Rightarrow> int list \<Rightarrow> int" where
  "bin_rcat n = foldl (\<lambda>u v. bin_cat u n v) 0"

fun bin_rsplit_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list" where
  "bin_rsplit_aux n m c bs =
    (if m = 0 | n = 0 then bs else
      let (a, b) = bin_split n c 
      in bin_rsplit_aux n (m - n) a (b # bs))"

definition bin_rsplit :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list" where
  "bin_rsplit n w = bin_rsplit_aux n (fst w) (snd w) []"

fun bin_rsplitl_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list" where
  "bin_rsplitl_aux n m c bs =
    (if m = 0 | n = 0 then bs else
      let (a, b) = bin_split (min m n) c 
      in bin_rsplitl_aux n (m - n) a (b # bs))"

definition bin_rsplitl :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list" where
  "bin_rsplitl n w = bin_rsplitl_aux n (fst w) (snd w) []"

declare bin_rsplit_aux.simps [simp del]
declare bin_rsplitl_aux.simps [simp del]

lemma bin_sign_cat: 
  "bin_sign (bin_cat x n y) = bin_sign x"
  by (induct n arbitrary: y) auto

lemma bin_cat_Suc_Bit:
  "bin_cat w (Suc n) (v BIT b) = bin_cat w n v BIT b"
  by auto

lemma bin_nth_cat: 
  "bin_nth (bin_cat x k y) n = 
    (if n < k then bin_nth y n else bin_nth x (n - k))"
  apply (induct k arbitrary: n y)
   apply clarsimp
  apply (case_tac n, auto)
  done

lemma bin_nth_split:
  "bin_split n c = (a, b) ==> 
    (ALL k. bin_nth a k = bin_nth c (n + k)) & 
    (ALL k. bin_nth b k = (k < n & bin_nth c k))"
  apply (induct n arbitrary: b c)
   apply clarsimp
  apply (clarsimp simp: Let_def split: ls_splits)
  apply (case_tac k)
  apply auto
  done

lemma bin_cat_assoc: 
  "bin_cat (bin_cat x m y) n z = bin_cat x (m + n) (bin_cat y n z)" 
  by (induct n arbitrary: z) auto

lemma bin_cat_assoc_sym:
  "bin_cat x m (bin_cat y n z) = bin_cat (bin_cat x (m - n) y) (min m n) z"
  apply (induct n arbitrary: z m, clarsimp)
  apply (case_tac m, auto)
  done

lemma bin_cat_zero [simp]: "bin_cat 0 n w = bintrunc n w"
  by (induct n arbitrary: w) auto

lemma bintr_cat1: 
  "bintrunc (k + n) (bin_cat a n b) = bin_cat (bintrunc k a) n b"
  by (induct n arbitrary: b) auto
    
lemma bintr_cat: "bintrunc m (bin_cat a n b) = 
    bin_cat (bintrunc (m - n) a) n (bintrunc (min m n) b)"
  by (rule bin_eqI) (auto simp: bin_nth_cat nth_bintr)
    
lemma bintr_cat_same [simp]: 
  "bintrunc n (bin_cat a n b) = bintrunc n b"
  by (auto simp add : bintr_cat)

lemma cat_bintr [simp]: 
  "bin_cat a n (bintrunc n b) = bin_cat a n b"
  by (induct n arbitrary: b) auto

lemma split_bintrunc: 
  "bin_split n c = (a, b) ==> b = bintrunc n c"
  by (induct n arbitrary: b c) (auto simp: Let_def split: ls_splits)

lemma bin_cat_split:
  "bin_split n w = (u, v) ==> w = bin_cat u n v"
  by (induct n arbitrary: v w) (auto simp: Let_def split: ls_splits)

lemma bin_split_cat:
  "bin_split n (bin_cat v n w) = (v, bintrunc n w)"
  by (induct n arbitrary: w) auto

lemma bin_split_zero [simp]: "bin_split n 0 = (0, 0)"
  by (induct n) auto

lemma bin_split_minus1 [simp]:
  "bin_split n -1 = (-1, bintrunc n -1)"
  by (induct n) auto

lemma bin_split_trunc:
  "bin_split (min m n) c = (a, b) ==> 
    bin_split n (bintrunc m c) = (bintrunc (m - n) a, b)"
  apply (induct n arbitrary: m b c, clarsimp)
  apply (simp add: bin_rest_trunc Let_def split: ls_splits)
  apply (case_tac m)
   apply (auto simp: Let_def split: ls_splits)
  done

lemma bin_split_trunc1:
  "bin_split n c = (a, b) ==> 
    bin_split n (bintrunc m c) = (bintrunc (m - n) a, bintrunc m b)"
  apply (induct n arbitrary: m b c, clarsimp)
  apply (simp add: bin_rest_trunc Let_def split: ls_splits)
  apply (case_tac m)
   apply (auto simp: Let_def split: ls_splits)
  done

lemma bin_cat_num:
  "bin_cat a n b = a * 2 ^ n + bintrunc n b"
  apply (induct n arbitrary: b, clarsimp)
  apply (simp add: Bit_def)
  done

lemma bin_split_num:
  "bin_split n b = (b div 2 ^ n, b mod 2 ^ n)"
  apply (induct n arbitrary: b, simp)
  apply (simp add: bin_rest_def zdiv_zmult2_eq)
  apply (case_tac b rule: bin_exhaust)
  apply simp
  apply (simp add: Bit_def mod_mult_mult1 p1mod22k bitval_def
              split: bit.split)
  done

subsection {* Miscellaneous lemmas *}

lemma nth_2p_bin: 
  "bin_nth (2 ^ n) m = (m = n)"
  apply (induct n arbitrary: m)
   apply clarsimp
   apply safe
   apply (case_tac m) 
    apply (auto simp: Bit_B0_2t [symmetric])
  done

(* for use when simplifying with bin_nth_Bit *)

lemma ex_eq_or:
  "(EX m. n = Suc m & (m = k | P m)) = (n = Suc k | (EX m. n = Suc m & P m))"
  by auto

end
