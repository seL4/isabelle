(*  Title:      HOL/Word/Misc_Auxiliary.thy
    Author:     Jeremy Dawson, NICTA
*)

section \<open>Generic auxiliary\<close>

theory Misc_Auxiliary
  imports Main
begin

subsection \<open>Arithmetic lemmas\<close>

lemma int_mod_lem: "0 < n \<Longrightarrow> 0 \<le> b \<and> b < n \<longleftrightarrow> b mod n = b"
  for b n :: int
  apply safe
    apply (erule (1) mod_pos_pos_trivial)
   apply (erule_tac [!] subst)
   apply auto
  done

lemma int_mod_ge: "a < n \<Longrightarrow> 0 < n \<Longrightarrow> a \<le> a mod n"
  for a n :: int
  by (metis dual_order.trans le_cases mod_pos_pos_trivial pos_mod_conj)

lemma int_mod_ge': "b < 0 \<Longrightarrow> 0 < n \<Longrightarrow> b + n \<le> b mod n"
  for b n :: int
  by (metis add_less_same_cancel2 int_mod_ge mod_add_self2)

lemma int_mod_le': "0 \<le> b - n \<Longrightarrow> b mod n \<le> b - n"
  for b n :: int
  by (metis minus_mod_self2 zmod_le_nonneg_dividend)

lemma emep1: "even n \<Longrightarrow> even d \<Longrightarrow> 0 \<le> d \<Longrightarrow> (n + 1) mod d = (n mod d) + 1"
  for n d :: int
  by (auto simp add: pos_zmod_mult_2 add.commute dvd_def)

lemma m1mod2k: "- 1 mod 2 ^ n = (2 ^ n - 1 :: int)"
  by (rule zmod_minus1) simp

lemma sub_inc_One: "Num.sub (Num.inc n) num.One = numeral n"
  by (metis add_diff_cancel add_neg_numeral_special(3) add_uminus_conv_diff numeral_inc)
  
lemma inc_BitM: "Num.inc (Num.BitM n) = num.Bit0 n"
  by (simp add: BitM_plus_one[symmetric] add_One)


subsection \<open>Lemmas on list operations\<close>

lemma butlast_power: "(butlast ^^ n) bl = take (length bl - n) bl"
  by (induct n) (auto simp: butlast_take)

lemma nth_rev: "n < length xs \<Longrightarrow> rev xs ! n = xs ! (length xs - 1 - n)"
  using rev_nth by simp

lemma nth_rev_alt: "n < length ys \<Longrightarrow> ys ! n = rev ys ! (length ys - Suc n)"
  by (simp add: nth_rev)

lemma hd_butlast: "length xs > 1 \<Longrightarrow> hd (butlast xs) = hd xs"
  by (cases xs) auto


subsection \<open>Implicit augmentation of list prefixes\<close>

primrec takefill :: "'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
    Z: "takefill fill 0 xs = []"
  | Suc: "takefill fill (Suc n) xs =
      (case xs of
        [] \<Rightarrow> fill # takefill fill n xs
      | y # ys \<Rightarrow> y # takefill fill n ys)"

lemma nth_takefill: "m < n \<Longrightarrow> takefill fill n l ! m = (if m < length l then l ! m else fill)"
  apply (induct n arbitrary: m l)
   apply clarsimp
  apply clarsimp
  apply (case_tac m)
   apply (simp split: list.split)
  apply (simp split: list.split)
  done

lemma takefill_alt: "takefill fill n l = take n l @ replicate (n - length l) fill"
  by (induct n arbitrary: l) (auto split: list.split)

lemma takefill_replicate [simp]: "takefill fill n (replicate m fill) = replicate n fill"
  by (simp add: takefill_alt replicate_add [symmetric])

lemma takefill_le': "n = m + k \<Longrightarrow> takefill x m (takefill x n l) = takefill x m l"
  by (induct m arbitrary: l n) (auto split: list.split)

lemma length_takefill [simp]: "length (takefill fill n l) = n"
  by (simp add: takefill_alt)

lemma take_takefill': "n = k + m \<Longrightarrow> take k (takefill fill n w) = takefill fill k w"
  by (induct k arbitrary: w n) (auto split: list.split)

lemma drop_takefill: "drop k (takefill fill (m + k) w) = takefill fill m (drop k w)"
  by (induct k arbitrary: w) (auto split: list.split)

lemma takefill_le [simp]: "m \<le> n \<Longrightarrow> takefill x m (takefill x n l) = takefill x m l"
  by (auto simp: le_iff_add takefill_le')

lemma take_takefill [simp]: "m \<le> n \<Longrightarrow> take m (takefill fill n w) = takefill fill m w"
  by (auto simp: le_iff_add take_takefill')

lemma takefill_append: "takefill fill (m + length xs) (xs @ w) = xs @ (takefill fill m w)"
  by (induct xs) auto

lemma takefill_same': "l = length xs \<Longrightarrow> takefill fill l xs = xs"
  by (induct xs arbitrary: l) auto

lemmas takefill_same [simp] = takefill_same' [OF refl]

lemma tf_rev:
  "n + k = m + length bl \<Longrightarrow> takefill x m (rev (takefill y n bl)) =
    rev (takefill y m (rev (takefill x k (rev bl))))"
  apply (rule nth_equalityI)
   apply (auto simp add: nth_takefill nth_rev)
  apply (rule_tac f = "\<lambda>n. bl ! n" in arg_cong)
  apply arith
  done

lemma takefill_minus: "0 < n \<Longrightarrow> takefill fill (Suc (n - 1)) w = takefill fill n w"
  by auto

lemmas takefill_Suc_cases =
  list.cases [THEN takefill.Suc [THEN trans]]

lemmas takefill_Suc_Nil = takefill_Suc_cases (1)
lemmas takefill_Suc_Cons = takefill_Suc_cases (2)

lemmas takefill_minus_simps = takefill_Suc_cases [THEN [2]
  takefill_minus [symmetric, THEN trans]]

lemma takefill_numeral_Nil [simp]:
  "takefill fill (numeral k) [] = fill # takefill fill (pred_numeral k) []"
  by (simp add: numeral_eq_Suc)

lemma takefill_numeral_Cons [simp]:
  "takefill fill (numeral k) (x # xs) = x # takefill fill (pred_numeral k) xs"
  by (simp add: numeral_eq_Suc)


subsection \<open>Auxiliary: Range projection\<close>

definition bl_of_nth :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list"
  where "bl_of_nth n f = map f (rev [0..<n])"

lemma bl_of_nth_simps [simp, code]:
  "bl_of_nth 0 f = []"
  "bl_of_nth (Suc n) f = f n # bl_of_nth n f"
  by (simp_all add: bl_of_nth_def)

lemma length_bl_of_nth [simp]: "length (bl_of_nth n f) = n"
  by (simp add: bl_of_nth_def)

lemma nth_bl_of_nth [simp]: "m < n \<Longrightarrow> rev (bl_of_nth n f) ! m = f m"
  by (simp add: bl_of_nth_def rev_map)

lemma bl_of_nth_inj: "(\<And>k. k < n \<Longrightarrow> f k = g k) \<Longrightarrow> bl_of_nth n f = bl_of_nth n g"
  by (simp add: bl_of_nth_def)

lemma bl_of_nth_nth_le: "n \<le> length xs \<Longrightarrow> bl_of_nth n (nth (rev xs)) = drop (length xs - n) xs"
  apply (induct n arbitrary: xs)
   apply clarsimp
  apply clarsimp
  apply (rule trans [OF _ hd_Cons_tl])
   apply (frule Suc_le_lessD)
   apply (simp add: nth_rev trans [OF drop_Suc drop_tl, symmetric])
   apply (subst hd_drop_conv_nth)
    apply force
   apply simp_all
  apply (rule_tac f = "\<lambda>n. drop n xs" in arg_cong)
  apply simp
  done

lemma bl_of_nth_nth [simp]: "bl_of_nth (length xs) ((!) (rev xs)) = xs"
  by (simp add: bl_of_nth_nth_le)

end
