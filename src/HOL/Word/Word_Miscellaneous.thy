(*  Title:      HOL/Word/Word_Miscellaneous.thy  *)

section \<open>Miscellaneous lemmas, of at least doubtful value\<close>

theory Word_Miscellaneous
  imports "HOL-Library.Bit" Misc_Numeric
begin

lemma power_minus_simp: "0 < n \<Longrightarrow> a ^ n = a * a ^ (n - 1)"
  by (auto dest: gr0_implies_Suc)

lemma funpow_minus_simp: "0 < n \<Longrightarrow> f ^^ n = f \<circ> f ^^ (n - 1)"
  by (auto dest: gr0_implies_Suc)

lemma power_numeral: "a ^ numeral k = a * a ^ (pred_numeral k)"
  by (simp add: numeral_eq_Suc)

lemma funpow_numeral [simp]: "f ^^ numeral k = f \<circ> f ^^ (pred_numeral k)"
  by (simp add: numeral_eq_Suc)

lemma replicate_numeral [simp]: "replicate (numeral k) x = x # replicate (pred_numeral k) x"
  by (simp add: numeral_eq_Suc)

lemma rco_alt: "(f \<circ> g) ^^ n \<circ> f = f \<circ> (g \<circ> f) ^^ n"
  apply (rule ext)
  apply (induct n)
   apply (simp_all add: o_def)
  done

lemma list_exhaust_size_gt0:
  assumes "\<And>a list. y = a # list \<Longrightarrow> P"
  shows "0 < length y \<Longrightarrow> P"
  apply (cases y)
   apply simp
  apply (rule assms)
  apply fastforce
  done

lemma list_exhaust_size_eq0:
  assumes "y = [] \<Longrightarrow> P"
  shows "length y = 0 \<Longrightarrow> P"
  apply (cases y)
   apply (rule assms)
   apply simp
  apply simp
  done

lemma size_Cons_lem_eq: "y = xa # list \<Longrightarrow> size y = Suc k \<Longrightarrow> size list = k"
  by auto

lemmas ls_splits = prod.split prod.split_asm if_split_asm

lemma not_B1_is_B0: "y \<noteq> 1 \<Longrightarrow> y = 0"
  for y :: bit
  by (cases y) auto

lemma B1_ass_B0:
  fixes y :: bit
  assumes y: "y = 0 \<Longrightarrow> y = 1"
  shows "y = 1"
  apply (rule classical)
  apply (drule not_B1_is_B0)
  apply (erule y)
  done

\<comment> \<open>simplifications for specific word lengths\<close>
lemmas n2s_ths [THEN eq_reflection] = add_2_eq_Suc add_2_eq_Suc'

lemmas s2n_ths = n2s_ths [symmetric]

lemma and_len: "xs = ys \<Longrightarrow> xs = ys \<and> length xs = length ys"
  by auto

lemma size_if: "size (if p then xs else ys) = (if p then size xs else size ys)"
  by auto

lemma tl_if: "tl (if p then xs else ys) = (if p then tl xs else tl ys)"
  by auto

lemma hd_if: "hd (if p then xs else ys) = (if p then hd xs else hd ys)"
  by auto

lemma if_Not_x: "(if p then \<not> x else x) = (p = (\<not> x))"
  by auto

lemma if_x_Not: "(if p then x else \<not> x) = (p = x)"
  by auto

lemma if_same_and: "(If p x y \<and> If p u v) = (if p then x \<and> u else y \<and> v)"
  by auto

lemma if_same_eq: "(If p x y  = (If p u v)) = (if p then x = u else y = v)"
  by auto

lemma if_same_eq_not: "(If p x y = (\<not> If p u v)) = (if p then x = (\<not> u) else y = (\<not> v))"
  by auto

\<comment> \<open>note -- \<open>if_Cons\<close> can cause blowup in the size, if \<open>p\<close> is complex, so make a simproc\<close>
lemma if_Cons: "(if p then x # xs else y # ys) = If p x y # If p xs ys"
  by auto

lemma if_single: "(if xc then [xab] else [an]) = [if xc then xab else an]"
  by auto

lemma if_bool_simps:
  "If p True y = (p \<or> y) \<and> If p False y = (\<not> p \<and> y) \<and>
    If p y True = (p \<longrightarrow> y) \<and> If p y False = (p \<and> y)"
  by auto

lemmas if_simps =
  if_x_Not if_Not_x if_cancel if_True if_False if_bool_simps

lemmas seqr = eq_reflection [where x = "size w"] for w (* FIXME: delete *)

lemma the_elemI: "y = {x} \<Longrightarrow> the_elem y = x"
  by simp

lemma nonemptyE: "S \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

lemma gt_or_eq_0: "0 < y \<or> 0 = y"
  for y :: nat
  by arith

lemmas xtr1 = xtrans(1)
lemmas xtr2 = xtrans(2)
lemmas xtr3 = xtrans(3)
lemmas xtr4 = xtrans(4)
lemmas xtr5 = xtrans(5)
lemmas xtr6 = xtrans(6)
lemmas xtr7 = xtrans(7)
lemmas xtr8 = xtrans(8)

lemmas nat_simps = diff_add_inverse2 diff_add_inverse
lemmas nat_iffs = le_add1 le_add2

lemma sum_imp_diff: "j = k + i \<Longrightarrow> j - i = k"
  for k :: nat
  by arith

lemmas pos_mod_sign2 = zless2 [THEN pos_mod_sign [where b = "2::int"]]
lemmas pos_mod_bound2 = zless2 [THEN pos_mod_bound [where b = "2::int"]]

lemma nmod2: "n mod 2 = 0 \<or> n mod 2 = 1"
  for n :: int
  by arith

lemmas eme1p = emep1 [simplified add.commute]

lemma le_diff_eq': "a \<le> c - b \<longleftrightarrow> b + a \<le> c"
  for a b c :: int
  by arith

lemma less_diff_eq': "a < c - b \<longleftrightarrow> b + a < c"
  for a b c :: int
  by arith

lemma diff_less_eq': "a - b < c \<longleftrightarrow> a < b + c"
  for a b c :: int
  by arith

lemmas m1mod22k = mult_pos_pos [OF zless2 zless2p, THEN zmod_minus1]

lemma z1pdiv2: "(2 * b + 1) div 2 = b"
  for b :: int
  by arith

lemmas zdiv_le_dividend = xtr3 [OF div_by_1 [symmetric] zdiv_mono2,
  simplified int_one_le_iff_zero_less, simplified]

lemma axxbyy: "a + m + m = b + n + n \<Longrightarrow> a = 0 \<or> a = 1 \<Longrightarrow> b = 0 \<or> b = 1 \<Longrightarrow> a = b \<and> m = n"
  for a b m n :: int
  by arith

lemma axxmod2: "(1 + x + x) mod 2 = 1 \<and> (0 + x + x) mod 2 = 0"
  for x :: int
  by arith

lemma axxdiv2: "(1 + x + x) div 2 = x \<and> (0 + x + x) div 2 = x"
  for x :: int
  by arith

lemmas iszero_minus =
  trans [THEN trans, OF iszero_def neg_equal_0_iff_equal iszero_def [symmetric]]

lemmas zadd_diff_inverse =
  trans [OF diff_add_cancel [symmetric] add.commute]

lemmas add_diff_cancel2 =
  add.commute [THEN diff_eq_eq [THEN iffD2]]

lemmas rdmods [symmetric] = mod_minus_eq
  mod_diff_left_eq mod_diff_right_eq mod_add_left_eq
  mod_add_right_eq mod_mult_right_eq mod_mult_left_eq

lemma mod_plus_right: "(a + x) mod m = (b + x) mod m \<longleftrightarrow> a mod m = b mod m"
  for a b m x :: nat
  by (induct x) (simp_all add: mod_Suc, arith)

lemma nat_minus_mod: "(n - n mod m) mod m = 0"
  for m n :: nat
  by (induct n) (simp_all add: mod_Suc)

lemmas nat_minus_mod_plus_right =
  trans [OF nat_minus_mod mod_0 [symmetric],
    THEN mod_plus_right [THEN iffD2], simplified]

lemmas push_mods' = mod_add_eq
  mod_mult_eq mod_diff_eq
  mod_minus_eq

lemmas push_mods = push_mods' [THEN eq_reflection]
lemmas pull_mods = push_mods [symmetric] rdmods [THEN eq_reflection]

lemma nat_mod_eq: "b < n \<Longrightarrow> a mod n = b mod n \<Longrightarrow> a mod n = b"
  for a b n :: nat
  by (induct a) auto

lemmas nat_mod_eq' = refl [THEN [2] nat_mod_eq]

lemma nat_mod_lem: "0 < n \<Longrightarrow> b < n \<longleftrightarrow> b mod n = b"
  for b n :: nat
  apply safe
   apply (erule nat_mod_eq')
  apply (erule subst)
  apply (erule mod_less_divisor)
  done

lemma mod_nat_add: "x < z \<Longrightarrow> y < z \<Longrightarrow> (x + y) mod z = (if x + y < z then x + y else x + y - z)"
  for x y z :: nat
  apply (rule nat_mod_eq)
   apply auto
  apply (rule trans)
   apply (rule le_mod_geq)
   apply simp
  apply (rule nat_mod_eq')
  apply arith
  done

lemma mod_nat_sub: "x < z \<Longrightarrow> (x - y) mod z = x - y"
  for x y :: nat
  by (rule nat_mod_eq') arith

lemma int_mod_eq: "0 \<le> b \<Longrightarrow> b < n \<Longrightarrow> a mod n = b mod n \<Longrightarrow> a mod n = b"
  for a b n :: int
  by (metis mod_pos_pos_trivial)

lemmas int_mod_eq' = mod_pos_pos_trivial (* FIXME delete *)

lemmas int_mod_le = zmod_le_nonneg_dividend (* FIXME: delete *)

lemma mod_add_if_z:
  "x < z \<Longrightarrow> y < z \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> x \<Longrightarrow> 0 \<le> z \<Longrightarrow>
    (x + y) mod z = (if x + y < z then x + y else x + y - z)"
  for x y z :: int
  by (auto intro: int_mod_eq)

lemma mod_sub_if_z:
  "x < z \<Longrightarrow> y < z \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> x \<Longrightarrow> 0 \<le> z \<Longrightarrow>
    (x - y) mod z = (if y \<le> x then x - y else x - y + z)"
  for x y z :: int
  by (auto intro: int_mod_eq)

lemmas zmde = mult_div_mod_eq [symmetric, THEN diff_eq_eq [THEN iffD2], symmetric]
lemmas mcl = mult_cancel_left [THEN iffD1, THEN make_pos_rule]

(* already have this for naturals, div_mult_self1/2, but not for ints *)
lemma zdiv_mult_self: "m \<noteq> 0 \<Longrightarrow> (a + m * n) div m = a div m + n"
  for a m n :: int
  apply (rule mcl)
   prefer 2
   apply (erule asm_rl)
  apply (simp add: zmde ring_distribs)
  done

lemma mod_power_lem: "a > 1 \<Longrightarrow> a ^ n mod a ^ m = (if m \<le> n then 0 else a ^ n)"
  for a :: int
  by (simp add: mod_eq_0_iff_dvd le_imp_power_dvd)

lemma pl_pl_rels: "a + b = c + d \<Longrightarrow> a \<ge> c \<and> b \<le> d \<or> a \<le> c \<and> b \<ge> d"
  for a b c d :: nat
  by arith

lemmas pl_pl_rels' = add.commute [THEN [2] trans, THEN pl_pl_rels]

lemma minus_eq: "m - k = m \<longleftrightarrow> k = 0 \<or> m = 0"
  for k m :: nat
  by arith

lemma pl_pl_mm: "a + b = c + d \<Longrightarrow> a - c = d - b"
  for a b c d :: nat
  by arith

lemmas pl_pl_mm' = add.commute [THEN [2] trans, THEN pl_pl_mm]

lemmas dme = div_mult_mod_eq
lemmas dtle = div_times_less_eq_dividend
lemmas th2 = order_trans [OF order_refl [THEN [2] mult_le_mono] div_times_less_eq_dividend]

lemma td_gal: "0 < c \<Longrightarrow> a \<ge> b * c \<longleftrightarrow> a div c \<ge> b"
  for a b c :: nat
  apply safe
   apply (erule (1) xtr4 [OF div_le_mono div_mult_self_is_m])
  apply (erule th2)
  done

lemmas td_gal_lt = td_gal [simplified not_less [symmetric], simplified]

lemmas div_mult_le = div_times_less_eq_dividend

lemmas sdl = div_nat_eqI

lemma given_quot: "f > 0 \<Longrightarrow> (f * l + (f - 1)) div f = l"
  for f l :: nat
  by (rule div_nat_eqI) (simp_all)

lemma given_quot_alt: "f > 0 \<Longrightarrow> (l * f + f - Suc 0) div f = l"
  for f l :: nat
  apply (frule given_quot)
  apply (rule trans)
   prefer 2
   apply (erule asm_rl)
  apply (rule_tac f="\<lambda>n. n div f" in arg_cong)
  apply (simp add : ac_simps)
  done

lemma diff_mod_le: "a < d \<Longrightarrow> b dvd d \<Longrightarrow> a - a mod b \<le> d - b"
  for a b d :: nat
  apply (unfold dvd_def)
  apply clarify
  apply (case_tac k)
   apply clarsimp
  apply clarify
  apply (cases "b > 0")
   apply (drule mult.commute [THEN xtr1])
   apply (frule (1) td_gal_lt [THEN iffD1])
   apply (clarsimp simp: le_simps)
   apply (rule minus_mod_eq_mult_div [symmetric, THEN [2] xtr4])
   apply (rule mult_mono)
      apply auto
  done

lemma less_le_mult': "w * c < b * c \<Longrightarrow> 0 \<le> c \<Longrightarrow> (w + 1) * c \<le> b * c"
  for b c w :: int
  apply (rule mult_right_mono)
   apply (rule zless_imp_add1_zle)
   apply (erule (1) mult_right_less_imp_less)
  apply assumption
  done

lemma less_le_mult: "w * c < b * c \<Longrightarrow> 0 \<le> c \<Longrightarrow> w * c + c \<le> b * c"
  for b c w :: int
  using less_le_mult' [of w c b] by (simp add: algebra_simps)

lemmas less_le_mult_minus = iffD2 [OF le_diff_eq less_le_mult,
  simplified left_diff_distrib]

lemma gen_minus: "0 < n \<Longrightarrow> f n = f (Suc (n - 1))"
  by auto

lemma mpl_lem: "j \<le> i \<Longrightarrow> k < j \<Longrightarrow> i - j + k < i"
  for i j k :: nat
  by arith

lemma nonneg_mod_div: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> (a mod b) \<and> 0 \<le> a div b"
  for a b :: int
  by (cases "b = 0") (auto intro: pos_imp_zdiv_nonneg_iff [THEN iffD2])

declare iszero_0 [intro]

lemma min_pm [simp]: "min a b + (a - b) = a"
  for a b :: nat
  by arith

lemma min_pm1 [simp]: "a - b + min a b = a"
  for a b :: nat
  by arith

lemma rev_min_pm [simp]: "min b a + (a - b) = a"
  for a b :: nat
  by arith

lemma rev_min_pm1 [simp]: "a - b + min b a = a"
  for a b :: nat
  by arith

lemma min_minus [simp]: "min m (m - k) = m - k"
  for m k :: nat
  by arith

lemma min_minus' [simp]: "min (m - k) m = m - k"
  for m k :: nat
  by arith

end
