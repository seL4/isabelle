(*  Title:      HOL/Library/Word.thy
    ID:         $Id$
    Author:     Sebastian Skalberg (TU Muenchen)
*)

theory Word = Main files "word_setup.ML":

subsection {* Auxilary Lemmas *}

text {* Amazing that these are necessary, but I can't find equivalent
ones in the other HOL theories. *}

lemma max_le [intro!]: "[| x \<le> z; y \<le> z |] ==> max x y \<le> z"
  by (simp add: max_def)

lemma max_mono:
  assumes mf: "mono f"
  shows       "max (f (x::'a::linorder)) (f y) \<le> f (max x y)"
proof -
  from mf and le_maxI1 [of x y]
  have fx: "f x \<le> f (max x y)"
    by (rule monoD)
  from mf and le_maxI2 [of y x]
  have fy: "f y \<le> f (max x y)"
    by (rule monoD)
  from fx and fy
  show "max (f x) (f y) \<le> f (max x y)"
    by auto
qed

lemma le_imp_power_le:
  assumes b0: "0 < (b::nat)"
  and     xy: "x \<le> y"
  shows       "b ^ x \<le> b ^ y"
proof (rule ccontr)
  assume "~ b ^ x \<le> b ^ y"
  hence bybx: "b ^ y < b ^ x"
    by simp
  have "y < x"
  proof (rule nat_power_less_imp_less [OF _ bybx])
    from b0
    show "0 < b"
      .
  qed
  with xy
  show False
    by simp
qed

lemma less_imp_power_less:
  assumes b1: "1 < (b::nat)"
  and     xy: "x < y"
  shows       "b ^ x < b ^ y"
proof (rule ccontr)
  assume "~ b ^ x < b ^ y"
  hence bybx: "b ^ y \<le> b ^ x"
    by simp
  have "y \<le> x"
  proof (rule power_le_imp_le_exp [OF _ bybx])
    from b1
    show "1 < b"
      .
  qed
  with xy
  show False
    by simp
qed

lemma [simp]: "1 < (b::nat) ==> (b ^ x \<le> b ^ y) = (x \<le> y)"
  apply rule
  apply (erule power_le_imp_le_exp)
  apply assumption
  apply (subgoal_tac "0 < b")
  apply (erule le_imp_power_le)
  apply assumption
  apply simp
  done

lemma [simp]: "1 < (b::nat) ==> (b ^ x < b ^ y) = (x < y)"
  apply rule
  apply (subgoal_tac "0 < b")
  apply (erule nat_power_less_imp_less)
  apply assumption
  apply simp
  apply (erule less_imp_power_less)
  apply assumption
  done

lemma power_le_imp_zle:
  assumes b1:   "1 < (b::int)"
  and     bxby: "b ^ x \<le> b ^ y"
  shows         "x \<le> y"
proof -
  from b1
  have nb1: "1 < nat b"
    by arith
  from b1
  have nb0: "0 \<le> b"
    by simp
  from bxby
  have "nat (b ^ x) \<le> nat (b ^ y)"
    by arith
  hence "nat b ^ x \<le> nat b ^ y"
    by (simp add: nat_power_eq [OF nb0])
  with power_le_imp_le_exp and nb1
  show "x \<le> y"
    by auto
qed

lemma zero_le_zpower [intro]:
  assumes b0: "0 \<le> (b::int)"
  shows       "0 \<le> b ^ n"
proof (induct n,simp)
  fix n
  assume ind: "0 \<le> b ^ n"
  have "b * 0 \<le> b * b ^ n"
  proof (subst mult_le_cancel_left,auto intro!: ind)
    assume "b < 0"
    with b0
    show "b ^ n \<le> 0"
      by simp
  qed
  thus "0 \<le> b ^ Suc n"
    by simp
qed

lemma zero_less_zpower [intro]:
  assumes b0: "0 < (b::int)"
  shows       "0 < b ^ n"
proof -
  from b0
  have b0': "0 \<le> b"
    by simp
  from b0
  have "0 < nat b"
    by simp
  hence "0 < nat b ^ n"
    by (rule zero_less_power)
  hence xx: "nat 0 < nat (b ^ n)"
    by (subst nat_power_eq [OF b0'],simp)
  show "0 < b ^ n"
    apply (subst nat_less_eq_zless [symmetric])
    apply simp
    apply (rule xx)
    done
qed

lemma power_less_imp_zless:
  assumes b0:   "0 < (b::int)"
  and     bxby: "b ^ x < b ^ y"
  shows         "x < y"
proof -
  from b0
  have nb0: "0 < nat b"
    by arith
  from b0
  have b0': "0 \<le> b"
    by simp
  have "nat (b ^ x) < nat (b ^ y)"
  proof (subst nat_less_eq_zless)
    show "0 \<le> b ^ x"
      by (rule zero_le_zpower [OF b0'])
  next
    show "b ^ x < b ^ y"
      by (rule bxby)
  qed
  hence "nat b ^ x < nat b ^ y"
    by (simp add: nat_power_eq [OF b0'])
  with nat_power_less_imp_less [OF nb0]
  show "x < y"
    .
qed

lemma le_imp_power_zle:
  assumes b0: "0 < (b::int)"
  and     xy: "x \<le> y"
  shows       "b ^ x \<le> b ^ y"
proof (rule ccontr)
  assume "~ b ^ x \<le> b ^ y"
  hence bybx: "b ^ y < b ^ x"
    by simp
  have "y < x"
  proof (rule power_less_imp_zless [OF _ bybx])
    from b0
    show "0 < b"
      .
  qed
  with xy
  show False
    by simp
qed

lemma less_imp_power_zless:
  assumes b1: "1 < (b::int)"
  and     xy: "x < y"
  shows       "b ^ x < b ^ y"
proof (rule ccontr)
  assume "~ b ^ x < b ^ y"
  hence bybx: "b ^ y \<le> b ^ x"
    by simp
  have "y \<le> x"
  proof (rule power_le_imp_zle [OF _ bybx])
    from b1
    show "1 < b"
      .
  qed
  with xy
  show False
    by simp
qed

lemma [simp]: "1 < (b::int) ==> (b ^ x \<le> b ^ y) = (x \<le> y)"
  apply rule
  apply (erule power_le_imp_zle)
  apply assumption
  apply (subgoal_tac "0 < b")
  apply (erule le_imp_power_zle)
  apply assumption
  apply simp
  done

lemma [simp]: "1 < (b::int) ==> (b ^ x < b ^ y) = (x < y)"
  apply rule
  apply (subgoal_tac "0 < b")
  apply (erule power_less_imp_zless)
  apply assumption
  apply simp
  apply (erule less_imp_power_zless)
  apply assumption
  done

lemma suc_zero_le: "[| 0 < x ; 0 < y |] ==> Suc 0 < x + y"
  by simp

lemma int_nat_two_exp: "2 ^ k = int (2 ^ k)"
  by (induct k,simp_all)

section {* Bits *}

datatype bit
  = Zero ("\<zero>")
  | One ("\<one>")

consts
  bitval :: "bit => int"

primrec
  "bitval \<zero> = 0"
  "bitval \<one> = 1"

consts
  bitnot :: "bit => bit"
  bitand :: "bit => bit => bit" (infixr "bitand" 35)
  bitor  :: "bit => bit => bit" (infixr "bitor"  30)
  bitxor :: "bit => bit => bit" (infixr "bitxor" 30)

syntax (xsymbols)
  bitnot :: "bit => bit"        ("\<not>\<^sub>b _" [40] 40)
  bitand :: "bit => bit => bit" (infixr "\<and>\<^sub>b" 35)
  bitor  :: "bit => bit => bit" (infixr "\<or>\<^sub>b" 30)
  bitxor :: "bit => bit => bit" (infixr "\<oplus>\<^sub>b" 30)

syntax (HTML output)
  bitnot :: "bit => bit"        ("\<not>\<^sub>b _" [40] 40)
  bitand :: "bit => bit => bit" (infixr "\<and>\<^sub>b" 35)
  bitor  :: "bit => bit => bit" (infixr "\<or>\<^sub>b" 30)
  bitxor :: "bit => bit => bit" (infixr "\<oplus>\<^sub>b" 30)

primrec
  bitnot_zero: "(bitnot \<zero>) = \<one>"
  bitnot_one : "(bitnot \<one>)  = \<zero>"

primrec
  bitand_zero: "(\<zero> bitand y) = \<zero>"
  bitand_one:  "(\<one> bitand y) = y"

primrec
  bitor_zero: "(\<zero> bitor y) = y"
  bitor_one:  "(\<one> bitor y) = \<one>"

primrec
  bitxor_zero: "(\<zero> bitxor y) = y"
  bitxor_one:  "(\<one> bitxor y) = (bitnot y)"

lemma [simp]: "(bitnot (bitnot b)) = b"
  by (cases b,simp_all)

lemma [simp]: "(b bitand b) = b"
  by (cases b,simp_all)

lemma [simp]: "(b bitor b) = b"
  by (cases b,simp_all)

lemma [simp]: "(b bitxor b) = \<zero>"
  by (cases b,simp_all)

section {* Bit Vectors *}

text {* First, a couple of theorems expressing case analysis and
induction principles for bit vectors. *}

lemma bit_list_cases:
  assumes empty: "w = [] ==> P w"
  and     zero:  "!!bs. w = \<zero> # bs ==> P w"
  and     one:   "!!bs. w = \<one> # bs ==> P w"
  shows   "P w"
proof (cases w)
  assume "w = []"
  thus ?thesis
    by (rule empty)
next
  fix b bs
  assume [simp]: "w = b # bs"
  show "P w"
  proof (cases b)
    assume "b = \<zero>"
    hence "w = \<zero> # bs"
      by simp
    thus ?thesis
      by (rule zero)
  next
    assume "b = \<one>"
    hence "w = \<one> # bs"
      by simp
    thus ?thesis
      by (rule one)
  qed
qed

lemma bit_list_induct:
  assumes empty: "P []"
  and     zero:  "!!bs. P bs ==> P (\<zero>#bs)"
  and     one:   "!!bs. P bs ==> P (\<one>#bs)"
  shows   "P w"
proof (induct w,simp_all add: empty)
  fix b bs
  assume [intro!]: "P bs"
  show "P (b#bs)"
    by (cases b,auto intro!: zero one)
qed

constdefs
  bv_msb :: "bit list => bit"
  "bv_msb w == if w = [] then \<zero> else hd w"
  bv_extend :: "[nat,bit,bit list]=>bit list"
  "bv_extend i b w == (replicate (i - length w) b) @ w"
  bv_not :: "bit list => bit list"
  "bv_not w == map bitnot w"

lemma bv_length_extend [simp]: "length w \<le> i ==> length (bv_extend i b w) = i"
  by (simp add: bv_extend_def)

lemma [simp]: "bv_not [] = []"
  by (simp add: bv_not_def)

lemma [simp]: "bv_not (b#bs) = (bitnot b) # bv_not bs"
  by (simp add: bv_not_def)

lemma [simp]: "bv_not (bv_not w) = w"
  by (rule bit_list_induct [of _ w],simp_all)

lemma [simp]: "bv_msb [] = \<zero>"
  by (simp add: bv_msb_def)

lemma [simp]: "bv_msb (b#bs) = b"
  by (simp add: bv_msb_def)

lemma [simp]: "0 < length w ==> bv_msb (bv_not w) = (bitnot (bv_msb w))"
  by (cases w,simp_all)

lemma [simp,intro]: "bv_msb w = \<one> ==> 0 < length w"
  by (cases w,simp_all)

lemma [simp]: "length (bv_not w) = length w"
  by (induct w,simp_all)

constdefs
  bv_to_nat :: "bit list => int"
  "bv_to_nat bv == number_of (foldl (%bn b. bn BIT (b = \<one>)) bin.Pls bv)"

lemma [simp]: "bv_to_nat [] = 0"
  by (simp add: bv_to_nat_def)

lemma pos_number_of: "(0::int)\<le> number_of w ==> number_of (w BIT b) = (2::int) * number_of w + (if b then 1 else 0)"
  by (induct w,auto,simp add: iszero_def)

lemma bv_to_nat_helper [simp]: "bv_to_nat (b # bs) = bitval b * 2 ^ length bs + bv_to_nat bs"
proof -
  def bv_to_nat' == "%base bv. number_of (foldl (% bn b. bn BIT (b = \<one>)) base bv)::int"
  have bv_to_nat'_def: "!!base bv. bv_to_nat' base bv == number_of (foldl (% bn b. bn BIT (b = \<one>)) base bv)::int"
    by (simp add: bv_to_nat'_def)
  have [rule_format]: "\<forall> base bs. (0::int) \<le> number_of base --> (\<forall> b. bv_to_nat' base (b # bs) = bv_to_nat' (base BIT (b = \<one>)) bs)"
    by (simp add: bv_to_nat'_def)
  have helper [rule_format]: "\<forall> base. (0::int) \<le> number_of base --> bv_to_nat' base bs = number_of base * 2 ^ length bs + bv_to_nat' bin.Pls bs"
  proof (induct bs,simp add: bv_to_nat'_def,clarify)
    fix x xs base
    assume ind [rule_format]: "\<forall> base. (0::int) \<le> number_of base --> bv_to_nat' base xs = number_of base * 2 ^ length xs + bv_to_nat' bin.Pls xs"
    assume base_pos: "(0::int) \<le> number_of base"
    def qq == "number_of base::int"
    show "bv_to_nat' base (x # xs) = number_of base * 2 ^ (length (x # xs)) + bv_to_nat' bin.Pls (x # xs)"
      apply (unfold bv_to_nat'_def)
      apply (simp only: foldl.simps)
      apply (fold bv_to_nat'_def)
      apply (subst ind [of "base BIT (x = \<one>)"])
      using base_pos
      apply simp
      apply (subst ind [of "bin.Pls BIT (x = \<one>)"])
      apply simp
      apply (subst pos_number_of [of "base" "x = \<one>"])
      using base_pos
      apply simp
      apply (subst pos_number_of [of "bin.Pls" "x = \<one>"])
      apply simp
      apply (fold qq_def)
      apply (simp add: ring_distrib)
      done
  qed
  show ?thesis
    apply (unfold bv_to_nat_def [of "b # bs"])
    apply (simp only: foldl.simps)
    apply (fold bv_to_nat'_def)
    apply (subst helper)
    apply simp
    apply (cases "b::bit")
    apply (simp add: bv_to_nat'_def bv_to_nat_def)
    apply (simp add: iszero_def)
    apply (simp add: bv_to_nat'_def bv_to_nat_def)
    done
qed

lemma bv_to_nat0 [simp]: "bv_to_nat (\<zero>#bs) = bv_to_nat bs"
  by simp

lemma bv_to_nat1 [simp]: "bv_to_nat (\<one>#bs) = 2 ^ length bs + bv_to_nat bs"
  by simp

lemma bv_to_nat_lower_range [intro,simp]: "0 \<le> bv_to_nat w"
  apply (induct w,simp_all)
  apply (case_tac a,simp_all)
  apply (rule add_increasing)
  apply auto
  done

lemma bv_to_nat_upper_range: "bv_to_nat w < 2 ^ length w"
proof (induct w,simp_all)
  fix b bs
  assume "bv_to_nat bs < 2 ^ length bs"
  show "bitval b * 2 ^ length bs + bv_to_nat bs < 2 * 2 ^ length bs"
  proof (cases b,simp_all)
    have "bv_to_nat bs < 2 ^ length bs"
      .
    also have "... < 2 * 2 ^ length bs"
      by auto
    finally show "bv_to_nat bs < 2 * 2 ^ length bs"
      by simp
  next
    have "bv_to_nat bs < 2 ^ length bs"
      .
    hence "2 ^ length bs + bv_to_nat bs < 2 ^ length bs + 2 ^ length bs"
      by arith
    also have "... = 2 * (2 ^ length bs)"
      by simp
    finally show "bv_to_nat bs < 2 ^ length bs"
      by simp
  qed
qed

lemma [simp]:
  assumes wn: "n \<le> length w"
  shows       "bv_extend n b w = w"
  by (simp add: bv_extend_def wn)

lemma [simp]:
  assumes wn: "length w < n"
  shows       "bv_extend n b w = bv_extend n b (b#w)"
proof -
  from wn
  have s: "n - Suc (length w) + 1 = n - length w"
    by arith
  have "bv_extend n b w = replicate (n - length w) b @ w"
    by (simp add: bv_extend_def)
  also have "... = replicate (n - Suc (length w) + 1) b @ w"
    by (subst s,rule)
  also have "... = (replicate (n - Suc (length w)) b @ replicate 1 b) @ w"
    by (subst replicate_add,rule)
  also have "... = replicate (n - Suc (length w)) b @ b # w"
    by simp
  also have "... = bv_extend n b (b#w)"
    by (simp add: bv_extend_def)
  finally show "bv_extend n b w = bv_extend n b (b#w)"
    .
qed

consts
  rem_initial :: "bit => bit list => bit list"

primrec
  "rem_initial b [] = []"
  "rem_initial b (x#xs) = (if b = x then rem_initial b xs else x#xs)"

lemma rem_initial_length: "length (rem_initial b w) \<le> length w"
  by (rule bit_list_induct [of _ w],simp_all (no_asm),safe,simp_all)

lemma rem_initial_equal:
  assumes p: "length (rem_initial b w) = length w"
  shows      "rem_initial b w = w"
proof -
  have "length (rem_initial b w) = length w --> rem_initial b w = w"
  proof (induct w,simp_all,clarify)
    fix xs
    assume "length (rem_initial b xs) = length xs --> rem_initial b xs = xs"
    assume f: "length (rem_initial b xs) = Suc (length xs)"
    with rem_initial_length [of b xs]
    show "rem_initial b xs = b#xs"
      by auto
  qed
  thus ?thesis
    ..
qed

lemma bv_extend_rem_initial: "bv_extend (length w) b (rem_initial b w) = w"
proof (induct w,simp_all,safe)
  fix xs
  assume ind: "bv_extend (length xs) b (rem_initial b xs) = xs"
  from rem_initial_length [of b xs]
  have [simp]: "Suc (length xs) - length (rem_initial b xs) = 1 + (length xs - length (rem_initial b xs))"
    by arith
  have "bv_extend (Suc (length xs)) b (rem_initial b xs) = replicate (Suc (length xs) - length (rem_initial b xs)) b @ (rem_initial b xs)"
    by (simp add: bv_extend_def)
  also have "... = replicate (1 + (length xs - length (rem_initial b xs))) b @ rem_initial b xs"
    by simp
  also have "... = (replicate 1 b @ replicate (length xs - length (rem_initial b xs)) b) @ rem_initial b xs"
    by (subst replicate_add,rule refl)
  also have "... = b # bv_extend (length xs) b (rem_initial b xs)"
    by (auto simp add: bv_extend_def [symmetric])
  also have "... = b # xs"
    by (simp add: ind)
  finally show "bv_extend (Suc (length xs)) b (rem_initial b xs) = b # xs"
    .
qed

lemma rem_initial_append1:
  assumes "rem_initial b xs ~= []"
  shows   "rem_initial b (xs @ ys) = rem_initial b xs @ ys"
proof -
  have "rem_initial b xs ~= [] --> rem_initial b (xs @ ys) = rem_initial b xs @ ys" (is "?P xs ys")
    by (induct xs,auto)
  thus ?thesis
    ..
qed

lemma rem_initial_append2:
  assumes "rem_initial b xs = []"
  shows   "rem_initial b (xs @ ys) = rem_initial b ys"
proof -
  have "rem_initial b xs = [] --> rem_initial b (xs @ ys) = rem_initial b ys" (is "?P xs ys")
    by (induct xs,auto)
  thus ?thesis
    ..
qed

constdefs
  norm_unsigned :: "bit list => bit list"
  "norm_unsigned == rem_initial \<zero>"

lemma [simp]: "norm_unsigned [] = []"
  by (simp add: norm_unsigned_def)

lemma [simp]: "norm_unsigned (\<zero>#bs) = norm_unsigned bs"
  by (simp add: norm_unsigned_def)

lemma [simp]: "norm_unsigned (\<one>#bs) = \<one>#bs"
  by (simp add: norm_unsigned_def)

lemma [simp]: "norm_unsigned (norm_unsigned w) = norm_unsigned w"
  by (rule bit_list_induct [of _ w],simp_all)

consts
  nat_to_bv_helper :: "int => bit list => bit list"

recdef nat_to_bv_helper "measure nat"
  "nat_to_bv_helper n = (%bs. (if n \<le> 0 then bs
                               else nat_to_bv_helper (n div 2) ((if n mod 2 = 0 then \<zero> else \<one>)#bs)))"

constdefs
  nat_to_bv :: "int => bit list"
  "nat_to_bv n == nat_to_bv_helper n []"

lemma nat_to_bv0 [simp]: "nat_to_bv 0 = []"
  by (simp add: nat_to_bv_def)

lemmas [simp del] = nat_to_bv_helper.simps

lemma n_div_2_cases:
  assumes n0  : "0 \<le> n"
  and     zero: "(n::int) = 0 ==> R"
  and     div : "[| n div 2 < n ; 0 < n |] ==> R"
  shows         "R"
proof (cases "n = 0")
  assume "n = 0"
  thus R
    by (rule zero)
next
  assume "n ~= 0"
  with n0
  have nn0: "0 < n"
    by simp
  hence "n div 2 < n"
    by arith
  from this and nn0
  show R
    by (rule div)
qed

lemma int_wf_ge_induct:
  assumes base:  "P (k::int)"
  and     ind :  "!!i. (!!j. [| k \<le> j ; j < i |] ==> P j) ==> P i"
  and     valid: "k \<le> i"
  shows          "P i"
proof -
  have a: "\<forall> j. k \<le> j \<and> j < i --> P j"
  proof (rule int_ge_induct)
    show "k \<le> i"
      .
  next
    show "\<forall> j. k \<le> j \<and> j < k --> P j"
      by auto
  next
    fix i
    assume "k \<le> i"
    assume a: "\<forall> j. k \<le> j \<and> j < i --> P j"
    have pi: "P i"
    proof (rule ind)
      fix j
      assume "k \<le> j" and "j < i"
      with a
      show "P j"
	by auto
    qed
    show "\<forall> j. k \<le> j \<and> j < i + 1 --> P j"
    proof auto
      fix j
      assume kj: "k \<le> j"
      assume ji: "j \<le> i"
      show "P j"
      proof (cases "j = i")
	assume "j = i"
	with pi
	show "P j"
	  by simp
      next
	assume "j ~= i"
	with ji
	have "j < i"
	  by simp
	with kj and a
	show "P j"
	  by blast
      qed
    qed
  qed
  show "P i"
  proof (rule ind)
    fix j
    assume "k \<le> j" and "j < i"
    with a
    show "P j"
      by auto
  qed
qed

lemma unfold_nat_to_bv_helper:
  "0 \<le> b ==> nat_to_bv_helper b l = nat_to_bv_helper b [] @ l"
proof -
  assume "0 \<le> b"
  have "\<forall>l. nat_to_bv_helper b l = nat_to_bv_helper b [] @ l"
  proof (rule int_wf_ge_induct [where ?i = b])
    show "0 \<le> b"
      .
  next
    show "\<forall> l. nat_to_bv_helper 0 l = nat_to_bv_helper 0 [] @ l"
      by (simp add: nat_to_bv_helper.simps)
  next
    fix n
    assume ind: "!!j. [| 0 \<le> j ; j < n |] ==> \<forall> l. nat_to_bv_helper j l = nat_to_bv_helper j [] @ l"
    show "\<forall>l. nat_to_bv_helper n l = nat_to_bv_helper n [] @ l"
    proof
      fix l
      show "nat_to_bv_helper n l = nat_to_bv_helper n [] @ l"
      proof (cases "n < 0")
	assume "n < 0"
	thus ?thesis
	  by (simp add: nat_to_bv_helper.simps)
      next
	assume "~n < 0"
	show ?thesis
	proof (rule n_div_2_cases [of n])
	  from prems
	  show "0 \<le> n"
	    by simp
	next
	  assume [simp]: "n = 0"
	  show ?thesis
	    apply (subst nat_to_bv_helper.simps [of n])
	    apply simp
	    done
	next
	  assume n2n: "n div 2 < n"
	  assume [simp]: "0 < n"
	  hence n20: "0 \<le> n div 2"
	    by arith
	  from ind [of "n div 2"] and n2n n20
	  have ind': "\<forall>l. nat_to_bv_helper (n div 2) l = nat_to_bv_helper (n div 2) [] @ l"
	    by blast
	  show ?thesis
	    apply (subst nat_to_bv_helper.simps [of n])
	    apply simp
	    apply (subst spec [OF ind',of "\<zero>#l"])
	    apply (subst spec [OF ind',of "\<one>#l"])
	    apply (subst spec [OF ind',of "[\<one>]"])
	    apply (subst spec [OF ind',of "[\<zero>]"])
	    apply simp
	    done
	qed
      qed
    qed
  qed
  thus ?thesis
    ..
qed

lemma nat_to_bv_non0 [simp]: "0 < n ==> nat_to_bv n = nat_to_bv (n div 2) @ [if n mod 2 = 0 then \<zero> else \<one>]"
proof -
  assume [simp]: "0 < n"
  show ?thesis
    apply (subst nat_to_bv_def [of n])
    apply (subst nat_to_bv_helper.simps [of n])
    apply (subst unfold_nat_to_bv_helper)
    using prems
    apply arith
    apply simp
    apply (subst nat_to_bv_def [of "n div 2"])
    apply auto
    using prems
    apply auto
    done
qed

lemma bv_to_nat_dist_append: "bv_to_nat (l1 @ l2) = bv_to_nat l1 * 2 ^ length l2 + bv_to_nat l2"
proof -
  have "\<forall>l2. bv_to_nat (l1 @ l2) = bv_to_nat l1 * 2 ^ length l2 + bv_to_nat l2"
  proof (induct l1,simp_all)
    fix x xs
    assume ind: "\<forall>l2. bv_to_nat (xs @ l2) = bv_to_nat xs * 2 ^ length l2 + bv_to_nat l2"
    show "\<forall>l2. bitval x * 2 ^ (length xs + length l2) + bv_to_nat xs * 2 ^ length l2 = (bitval x * 2 ^ length xs + bv_to_nat xs) * 2 ^ length l2"
    proof
      fix l2
      show "bitval x * 2 ^ (length xs + length l2) + bv_to_nat xs * 2 ^ length l2 = (bitval x * 2 ^ length xs + bv_to_nat xs) * 2 ^ length l2"
      proof -
	have "(2::int) ^ (length xs + length l2) = 2 ^ length xs * 2 ^ length l2"
	  by (induct "length xs",simp_all)
	hence "bitval x * 2 ^ (length xs + length l2) + bv_to_nat xs * 2 ^ length l2 =
	  bitval x * 2 ^ length xs * 2 ^ length l2 + bv_to_nat xs * 2 ^ length l2"
	  by simp
	also have "... = (bitval x * 2 ^ length xs + bv_to_nat xs) * 2 ^ length l2"
	  by (simp add: ring_distrib)
	finally show ?thesis .
      qed
    qed
  qed
  thus ?thesis
    ..
qed

lemma bv_nat_bv [simp]:
  assumes n0: "0 \<le> n"
  shows       "bv_to_nat (nat_to_bv n) = n"
proof -
  have "0 \<le> n --> bv_to_nat (nat_to_bv n) = n"
  proof (rule int_wf_ge_induct [where ?k = 0],simp_all,clarify)
    fix n
    assume ind: "!!j. [| 0 \<le> j; j < n |] ==> bv_to_nat (nat_to_bv j) = j"
    assume n0: "0 \<le> n"
    show "bv_to_nat (nat_to_bv n) = n"
    proof (rule n_div_2_cases [of n])
      show "0 \<le> n"
	.
    next
      assume [simp]: "n = 0"
      show ?thesis
	by simp
    next
      assume nn: "n div 2 < n"
      assume n0: "0 < n"
      hence n20: "0 \<le> n div 2"
	by arith
      from ind and n20 nn
      have ind': "bv_to_nat (nat_to_bv (n div 2)) = n div 2"
	by blast
      from n0 have n0': "~ n \<le> 0"
	by simp
      show ?thesis
	apply (subst nat_to_bv_def)
	apply (subst nat_to_bv_helper.simps [of n])
	apply (simp add: n0' split del: split_if)
	apply (subst unfold_nat_to_bv_helper)
	apply (rule n20)
	apply (subst bv_to_nat_dist_append)
	apply (fold nat_to_bv_def)
	apply (simp add: ind' split del: split_if)
	apply (cases "n mod 2 = 0")
      proof simp_all
	assume "n mod 2 = 0"
	with zmod_zdiv_equality [of n 2]
	show "n div 2 * 2 = n"
	  by simp
      next
	assume "n mod 2 = 1"
	with zmod_zdiv_equality [of n 2]
	show "n div 2 * 2 + 1 = n"
	  by simp
      qed
    qed
  qed
  with n0
  show ?thesis
    by auto
qed

lemma [simp]: "bv_to_nat (norm_unsigned w) = bv_to_nat w"
  by (rule bit_list_induct,simp_all)

lemma [simp]: "length (norm_unsigned w) \<le> length w"
  by (rule bit_list_induct,simp_all)

lemma bv_to_nat_rew_msb: "bv_msb w = \<one> ==> bv_to_nat w = 2 ^ (length w - 1) + bv_to_nat (tl w)"
  by (rule bit_list_cases [of w],simp_all)

lemma norm_unsigned_result: "norm_unsigned xs = [] \<or> bv_msb (norm_unsigned xs) = \<one>"
proof (rule length_induct [of _ xs])
  fix xs :: "bit list"
  assume ind: "\<forall>ys. length ys < length xs --> norm_unsigned ys = [] \<or> bv_msb (norm_unsigned ys) = \<one>"
  show "norm_unsigned xs = [] \<or> bv_msb (norm_unsigned xs) = \<one>"
  proof (rule bit_list_cases [of xs],simp_all)
    fix bs
    assume [simp]: "xs = \<zero>#bs"
    from ind
    have "length bs < length xs --> norm_unsigned bs = [] \<or> bv_msb (norm_unsigned bs) = \<one>"
      ..
    thus "norm_unsigned bs = [] \<or> bv_msb (norm_unsigned bs) = \<one>"
      by simp
  qed
qed

lemma norm_empty_bv_to_nat_zero:
  assumes nw: "norm_unsigned w = []"
  shows       "bv_to_nat w = 0"
proof -
  have "bv_to_nat w = bv_to_nat (norm_unsigned w)"
    by simp
  also have "... = bv_to_nat []"
    by (subst nw,rule)
  also have "... = 0"
    by simp
  finally show ?thesis .
qed

lemma bv_to_nat_lower_limit:
  assumes w0: "0 < bv_to_nat w"
  shows         "2 ^ (length (norm_unsigned w) - 1) \<le> bv_to_nat w"
proof -
  from w0 and norm_unsigned_result [of w]
  have msbw: "bv_msb (norm_unsigned w) = \<one>"
    by (auto simp add: norm_empty_bv_to_nat_zero)
  have "2 ^ (length (norm_unsigned w) - 1) \<le> bv_to_nat (norm_unsigned w)"
    by (subst bv_to_nat_rew_msb [OF msbw],simp)
  thus ?thesis
    by simp
qed

lemmas [simp del] = nat_to_bv_non0

lemma norm_unsigned_length [intro!]: "length (norm_unsigned w) \<le> length w"
  by (subst norm_unsigned_def,rule rem_initial_length)

lemma norm_unsigned_equal: "length (norm_unsigned w) = length w ==> norm_unsigned w = w"
  by (simp add: norm_unsigned_def,rule rem_initial_equal)

lemma bv_extend_norm_unsigned: "bv_extend (length w) \<zero> (norm_unsigned w) = w"
  by (simp add: norm_unsigned_def,rule bv_extend_rem_initial)

lemma norm_unsigned_append1 [simp]: "norm_unsigned xs \<noteq> [] ==> norm_unsigned (xs @ ys) = norm_unsigned xs @ ys"
  by (simp add: norm_unsigned_def,rule rem_initial_append1)

lemma norm_unsigned_append2 [simp]: "norm_unsigned xs = [] ==> norm_unsigned (xs @ ys) = norm_unsigned ys"
  by (simp add: norm_unsigned_def,rule rem_initial_append2)

lemma bv_to_nat_zero_imp_empty:
  assumes "bv_to_nat w = 0"
  shows   "norm_unsigned w = []"
proof -
  have "bv_to_nat w = 0 --> norm_unsigned w = []"
    apply (rule bit_list_induct [of _ w],simp_all)
    apply (subgoal_tac "0 < 2 ^ length bs + bv_to_nat bs")
    apply simp
    apply (subgoal_tac "(0::int) < 2 ^ length bs")
    apply (subgoal_tac "0 \<le> bv_to_nat bs")
    apply arith
    apply auto
    done
  thus ?thesis
    ..
qed

lemma bv_to_nat_nzero_imp_nempty:
  assumes "bv_to_nat w \<noteq> 0"
  shows   "norm_unsigned w \<noteq> []"
proof -
  have "bv_to_nat w \<noteq> 0 --> norm_unsigned w \<noteq> []"
    by (rule bit_list_induct [of _ w],simp_all)
  thus ?thesis
    ..
qed

lemma nat_helper1:
  assumes ass: "nat_to_bv (bv_to_nat w) = norm_unsigned w"
  shows        "nat_to_bv (2 * bv_to_nat w + bitval x) = norm_unsigned (w @ [x])"
proof (cases x)
  assume [simp]: "x = \<one>"
  show ?thesis
    apply (simp add: nat_to_bv_non0)
    apply safe
  proof -
    fix q
    assume "(2 * bv_to_nat w) + 1 = 2 * q"
    hence orig: "(2 * bv_to_nat w + 1) mod 2 = 2 * q mod 2" (is "?lhs = ?rhs")
      by simp
    have "?lhs = (1 + 2 * bv_to_nat w) mod 2"
      by (simp add: add_commute)
    also have "... = 1"
      by (simp add: zmod_zadd1_eq)
    finally have eq1: "?lhs = 1" .
    have "?rhs  = 0"
      by simp
    with orig and eq1
    have "(1::int) = 0"
      by simp
    thus "nat_to_bv ((2 * bv_to_nat w + 1) div 2) @ [\<zero>] = norm_unsigned (w @ [\<one>])"
      by simp
  next
    have "nat_to_bv ((2 * bv_to_nat w + 1) div 2) @ [\<one>] = nat_to_bv ((1 + 2 * bv_to_nat w) div 2) @ [\<one>]"
      by (simp add: add_commute)
    also have "... = nat_to_bv (bv_to_nat w) @ [\<one>]"
      by (subst zdiv_zadd1_eq,simp)
    also have "... = norm_unsigned w @ [\<one>]"
      by (subst ass,rule refl)
    also have "... = norm_unsigned (w @ [\<one>])"
      by (cases "norm_unsigned w",simp_all)
    finally show "nat_to_bv ((2 * bv_to_nat w + 1) div 2) @ [\<one>] = norm_unsigned (w @ [\<one>])"
      .
  qed
next
  assume [simp]: "x = \<zero>"
  show ?thesis
  proof (cases "bv_to_nat w = 0")
    assume "bv_to_nat w = 0"
    thus ?thesis
      by (simp add: bv_to_nat_zero_imp_empty)
  next
    assume "bv_to_nat w \<noteq> 0"
    thus ?thesis
      apply simp
      apply (subst nat_to_bv_non0)
      apply simp
      apply auto
      apply (cut_tac bv_to_nat_lower_range [of w])
      apply arith
      apply (subst ass)
      apply (cases "norm_unsigned w")
      apply (simp_all add: norm_empty_bv_to_nat_zero)
      done
  qed
qed

lemma nat_helper2: "nat_to_bv (2 ^ length xs + bv_to_nat xs) = \<one> # xs"
proof -
  have "\<forall>xs. nat_to_bv (2 ^ length (rev xs) + bv_to_nat (rev xs)) = \<one> # (rev xs)" (is "\<forall>xs. ?P xs")
  proof
    fix xs
    show "?P xs"
    proof (rule length_induct [of _ xs])
      fix xs :: "bit list"
      assume ind: "\<forall>ys. length ys < length xs --> ?P ys"
      show "?P xs"
      proof (cases xs)
	assume [simp]: "xs = []"
	show ?thesis
	  by (simp add: nat_to_bv_non0)
      next
	fix y ys
	assume [simp]: "xs = y # ys"
	show ?thesis
	  apply simp
	  apply (subst bv_to_nat_dist_append)
	  apply simp
	proof -
	  have "nat_to_bv (2 * 2 ^ length ys + (bv_to_nat (rev ys) * 2 + bitval y)) =
	    nat_to_bv (2 * (2 ^ length ys + bv_to_nat (rev ys)) + bitval y)"
	    by (simp add: add_ac mult_ac)
	  also have "... = nat_to_bv (2 * (bv_to_nat (\<one>#rev ys)) + bitval y)"
	    by simp
	  also have "... = norm_unsigned (\<one>#rev ys) @ [y]"
	  proof -
	    from ind
	    have "nat_to_bv (2 ^ length (rev ys) + bv_to_nat (rev ys)) = \<one> # rev ys"
	      by auto
	    hence [simp]: "nat_to_bv (2 ^ length ys + bv_to_nat (rev ys)) = \<one> # rev ys"
	      by simp
	    show ?thesis
	      apply (subst nat_helper1)
	      apply simp_all
	      done
	  qed
	  also have "... = (\<one>#rev ys) @ [y]"
	    by simp
	  also have "... = \<one> # rev ys @ [y]"
	    by simp
	  finally show "nat_to_bv (2 * 2 ^ length ys + (bv_to_nat (rev ys) * 2 + bitval y)) = \<one> # rev ys @ [y]"
	    .
	qed
      qed
    qed
  qed
  hence "nat_to_bv (2 ^ length (rev (rev xs)) + bv_to_nat (rev (rev xs))) = \<one> # rev (rev xs)"
    ..
  thus ?thesis
    by simp
qed

lemma nat_bv_nat [simp]: "nat_to_bv (bv_to_nat w) = norm_unsigned w"
proof (rule bit_list_induct [of _ w],simp_all)
  fix xs
  assume "nat_to_bv (bv_to_nat xs) = norm_unsigned xs"
  have "bv_to_nat xs = bv_to_nat (norm_unsigned xs)"
    by simp
  have "bv_to_nat xs < 2 ^ length xs"
    by (rule bv_to_nat_upper_range)
  show "nat_to_bv (2 ^ length xs + bv_to_nat xs) = \<one> # xs"
    by (rule nat_helper2)
qed

lemma [simp]: "bv_to_nat (norm_unsigned xs) = bv_to_nat xs"
  by (rule bit_list_induct [of _ w],simp_all)

lemma bv_to_nat_qinj:
  assumes one: "bv_to_nat xs = bv_to_nat ys"
  and     len: "length xs = length ys"
  shows        "xs = ys"
proof -
  from one
  have "nat_to_bv (bv_to_nat xs) = nat_to_bv (bv_to_nat ys)"
    by simp
  hence xsys: "norm_unsigned xs = norm_unsigned ys"
    by simp
  have "xs = bv_extend (length xs) \<zero> (norm_unsigned xs)"
    by (simp add: bv_extend_norm_unsigned)
  also have "... = bv_extend (length ys) \<zero> (norm_unsigned ys)"
    by (simp add: xsys len)
  also have "... = ys"
    by (simp add: bv_extend_norm_unsigned)
  finally show ?thesis .
qed

lemma norm_unsigned_nat_to_bv [simp]:
  assumes [simp]: "0 \<le> n"
  shows "norm_unsigned (nat_to_bv n) = nat_to_bv n"
proof -
  have "norm_unsigned (nat_to_bv n) = nat_to_bv (bv_to_nat (norm_unsigned (nat_to_bv n)))"
    by (subst nat_bv_nat,simp)
  also have "... = nat_to_bv n"
    by simp
  finally show ?thesis .
qed

lemma length_nat_to_bv_upper_limit:
  assumes nk: "n \<le> 2 ^ k - 1"
  shows       "length (nat_to_bv n) \<le> k"
proof (cases "n \<le> 0")
  assume "n \<le> 0"
  thus ?thesis
    by (simp add: nat_to_bv_def nat_to_bv_helper.simps)
next
  assume "~ n \<le> 0"
  hence n0: "0 < n"
    by simp
  hence n00: "0 \<le> n"
    by simp
  show ?thesis
  proof (rule ccontr)
    assume "~ length (nat_to_bv n) \<le> k"
    hence "k < length (nat_to_bv n)"
      by simp
    hence "k \<le> length (nat_to_bv n) - 1"
      by arith
    hence "(2::int) ^ k \<le> 2 ^ (length (nat_to_bv n) - 1)"
      by simp
    also have "... = 2 ^ (length (norm_unsigned (nat_to_bv n)) - 1)"
      by (simp add: n00)
    also have "... \<le> bv_to_nat (nat_to_bv n)"
      by (rule bv_to_nat_lower_limit,simp add: n00 n0)
    also have "... = n"
      by (simp add: n00)
    finally have "2 ^ k \<le> n" .
    with n0
    have "2 ^ k - 1 < n"
      by arith
    with nk
    show False
      by simp
  qed
qed

lemma length_nat_to_bv_lower_limit:
  assumes nk: "2 ^ k \<le> n"
  shows       "k < length (nat_to_bv n)"
proof (rule ccontr)
  have "(0::int) \<le> 2 ^ k"
    by auto
  with nk
  have [simp]: "0 \<le> n"
    by auto
  assume "~ k < length (nat_to_bv n)"
  hence lnk: "length (nat_to_bv n) \<le> k"
    by simp
  have "n = bv_to_nat (nat_to_bv n)"
    by simp
  also have "... < 2 ^ length (nat_to_bv n)"
    by (rule bv_to_nat_upper_range)
  also from lnk have "... \<le> 2 ^ k"
    by simp
  finally have "n < 2 ^ k" .
  with nk
  show False
    by simp
qed

section {* Unsigned Arithmetic Operations *}

constdefs
  bv_add :: "[bit list, bit list ] => bit list"
  "bv_add w1 w2 == nat_to_bv (bv_to_nat w1 + bv_to_nat w2)"

lemma [simp]: "bv_add (norm_unsigned w1) w2 = bv_add w1 w2"
  by (simp add: bv_add_def)

lemma [simp]: "bv_add w1 (norm_unsigned w2) = bv_add w1 w2"
  by (simp add: bv_add_def)

lemma [simp]: "norm_unsigned (bv_add w1 w2) = bv_add w1 w2"
  apply (simp add: bv_add_def)
  apply (rule norm_unsigned_nat_to_bv)
  apply (subgoal_tac "0 \<le> bv_to_nat w1")
  apply (subgoal_tac "0 \<le> bv_to_nat w2")
  apply arith
  apply simp_all
  done

lemma bv_add_length: "length (bv_add w1 w2) \<le> Suc (max (length w1) (length w2))"
proof (unfold bv_add_def,rule length_nat_to_bv_upper_limit)
  from bv_to_nat_upper_range [of w1] and bv_to_nat_upper_range [of w2]
  have "bv_to_nat w1 + bv_to_nat w2 \<le> (2 ^ length w1 - 1) + (2 ^ length w2 - 1)"
    by arith
  also have "... \<le> max (2 ^ length w1 - 1) (2 ^ length w2 - 1) + max (2 ^ length w1 - 1) (2 ^ length w2 - 1)"
    by (rule add_mono,safe intro!: le_maxI1 le_maxI2)
  also have "... = 2 * max (2 ^ length w1 - 1) (2 ^ length w2 - 1)"
    by simp
  also have "... \<le> 2 ^ Suc (max (length w1) (length w2)) - 2"
  proof (cases "length w1 \<le> length w2")
    assume [simp]: "length w1 \<le> length w2"
    hence "(2::int) ^ length w1 \<le> 2 ^ length w2"
      by simp
    hence [simp]: "(2::int) ^ length w1 - 1 \<le> 2 ^ length w2 - 1"
      by arith
    show ?thesis
      by (simp split: split_max)
  next
    assume [simp]: "~ (length w1 \<le> length w2)"
    have "~ ((2::int) ^ length w1 - 1 \<le> 2 ^ length w2 - 1)"
    proof
      assume "(2::int) ^ length w1 - 1 \<le> 2 ^ length w2 - 1"
      hence "((2::int) ^ length w1 - 1) + 1 \<le> (2 ^ length w2 - 1) + 1"
	by (rule add_right_mono)
      hence "(2::int) ^ length w1 \<le> 2 ^ length w2"
	by simp
      hence "length w1 \<le> length w2"
	by simp
      thus False
	by simp
    qed
    thus ?thesis
      by (simp split: split_max)
  qed
  finally show "bv_to_nat w1 + bv_to_nat w2 \<le> 2 ^ Suc (max (length w1) (length w2)) - 1"
    by arith
qed

constdefs
  bv_mult :: "[bit list, bit list ] => bit list"
  "bv_mult w1 w2 == nat_to_bv (bv_to_nat w1 * bv_to_nat w2)"

lemma [simp]: "bv_mult (norm_unsigned w1) w2 = bv_mult w1 w2"
  by (simp add: bv_mult_def)

lemma [simp]: "bv_mult w1 (norm_unsigned w2) = bv_mult w1 w2"
  by (simp add: bv_mult_def)

lemma [simp]: "norm_unsigned (bv_mult w1 w2) = bv_mult w1 w2"
  apply (simp add: bv_mult_def)
  apply (rule norm_unsigned_nat_to_bv)
  apply (subgoal_tac "0 * 0 \<le> bv_to_nat w1 * bv_to_nat w2")
  apply simp
  apply (rule mult_mono,simp_all)
  done

lemma bv_mult_length: "length (bv_mult w1 w2) \<le> length w1 + length w2"
proof (unfold bv_mult_def,rule length_nat_to_bv_upper_limit)
  from bv_to_nat_upper_range [of w1] and bv_to_nat_upper_range [of w2]
  have h: "bv_to_nat w1 \<le> 2 ^ length w1 - 1 \<and> bv_to_nat w2 \<le> 2 ^ length w2 - 1"
    by arith
  have "bv_to_nat w1 * bv_to_nat w2 \<le> (2 ^ length w1 - 1) * (2 ^ length w2 - 1)"
    apply (cut_tac h)
    apply (rule mult_mono)
    apply auto
    done
  also have "... < 2 ^ length w1 * 2 ^ length w2"
    by (rule mult_strict_mono,auto)
  also have "... = 2 ^ (length w1 + length w2)"
    by (simp add: power_add)
  finally show "bv_to_nat w1 * bv_to_nat w2 \<le> 2 ^ (length w1 + length w2) - 1"
    by arith
qed

section {* Signed Vectors *}

consts
  norm_signed :: "bit list => bit list"

primrec
  norm_signed_Nil: "norm_signed [] = []"
  norm_signed_Cons: "norm_signed (b#bs) = (case b of \<zero> => if norm_unsigned bs = [] then [] else b#norm_unsigned bs | \<one> => b#rem_initial b bs)"

lemma [simp]: "norm_signed [\<zero>] = []"
  by simp

lemma [simp]: "norm_signed [\<one>] = [\<one>]"
  by simp

lemma [simp]: "norm_signed (\<zero>#\<one>#xs) = \<zero>#\<one>#xs"
  by simp

lemma [simp]: "norm_signed (\<zero>#\<zero>#xs) = norm_signed (\<zero>#xs)"
  by simp

lemma [simp]: "norm_signed (\<one>#\<zero>#xs) = \<one>#\<zero>#xs"
  by simp

lemma [simp]: "norm_signed (\<one>#\<one>#xs) = norm_signed (\<one>#xs)"
  by simp

lemmas [simp del] = norm_signed_Cons

constdefs
  int_to_bv :: "int => bit list"
  "int_to_bv n == if 0 \<le> n
                 then norm_signed (\<zero>#nat_to_bv n)
                 else norm_signed (bv_not (\<zero>#nat_to_bv (-n- 1)))"

lemma int_to_bv_ge0 [simp]: "0 \<le> n ==> int_to_bv n = norm_signed (\<zero> # nat_to_bv n)"
  by (simp add: int_to_bv_def)

lemma int_to_bv_lt0 [simp]: "n < 0 ==> int_to_bv n = norm_signed (bv_not (\<zero>#nat_to_bv (-n- 1)))"
  by (simp add: int_to_bv_def)

lemma [simp]: "norm_signed (norm_signed w) = norm_signed w"
proof (rule bit_list_induct [of _ w],simp_all)
  fix xs
  assume "norm_signed (norm_signed xs) = norm_signed xs"
  show "norm_signed (norm_signed (\<zero>#xs)) = norm_signed (\<zero>#xs)"
  proof (rule bit_list_cases [of xs],simp_all)
    fix ys
    assume [symmetric,simp]: "xs = \<zero>#ys"
    show "norm_signed (norm_signed (\<zero>#ys)) = norm_signed (\<zero>#ys)"
      by simp
  qed
next
  fix xs
  assume "norm_signed (norm_signed xs) = norm_signed xs"
  show "norm_signed (norm_signed (\<one>#xs)) = norm_signed (\<one>#xs)"
  proof (rule bit_list_cases [of xs],simp_all)
    fix ys
    assume [symmetric,simp]: "xs = \<one>#ys"
    show "norm_signed (norm_signed (\<one>#ys)) = norm_signed (\<one>#ys)"
      by simp
  qed
qed

constdefs
  bv_to_int :: "bit list => int"
  "bv_to_int w == case bv_msb w of \<zero> => bv_to_nat w | \<one> => -(bv_to_nat (bv_not w) + 1)"

lemma [simp]: "bv_to_int [] = 0"
  by (simp add: bv_to_int_def)

lemma [simp]: "bv_to_int (\<zero>#bs) = bv_to_nat bs"
  by (simp add: bv_to_int_def)

lemma [simp]: "bv_to_int (\<one>#bs) = -(bv_to_nat (bv_not bs) + 1)"
  by (simp add: bv_to_int_def)

lemma [simp]: "bv_to_int (norm_signed w) = bv_to_int w"
proof (rule bit_list_induct [of _ w],simp_all)
  fix xs
  assume ind: "bv_to_int (norm_signed xs) = bv_to_int xs"
  show "bv_to_int (norm_signed (\<zero>#xs)) = bv_to_nat xs"
  proof (rule bit_list_cases [of xs],simp_all)
    fix ys
    assume [simp]: "xs = \<zero>#ys"
    from ind
    show "bv_to_int (norm_signed (\<zero>#ys)) = bv_to_nat ys"
      by simp
  qed
next
  fix xs
  assume ind: "bv_to_int (norm_signed xs) = bv_to_int xs"
  show "bv_to_int (norm_signed (\<one>#xs)) = - bv_to_nat (bv_not xs) + -1"
  proof (rule bit_list_cases [of xs],simp_all)
    fix ys
    assume [simp]: "xs = \<one>#ys"
    from ind
    show "bv_to_int (norm_signed (\<one>#ys)) = - bv_to_nat (bv_not ys) + -1"
      by simp
  qed
qed

lemma bv_to_int_upper_range: "bv_to_int w < 2 ^ (length w - 1)"
proof (rule bit_list_cases [of w],simp_all)
  fix bs
  show "bv_to_nat bs < 2 ^ length bs"
    by (rule bv_to_nat_upper_range)
next
  fix bs
  have "- (bv_to_nat (bv_not bs)) + -1 \<le> 0 + 0"
    by (rule add_mono,simp_all)
  also have "... < 2 ^ length bs"
    by (induct bs,simp_all)
  finally show "- (bv_to_nat (bv_not bs)) + -1 < 2 ^ length bs"
    .
qed

lemma bv_to_int_lower_range: "- (2 ^ (length w - 1)) \<le> bv_to_int w"
proof (rule bit_list_cases [of w],simp_all)
  fix bs :: "bit list"
  have "- (2 ^ length bs) \<le> (0::int)"
    by (induct bs,simp_all)
  also have "... \<le> bv_to_nat bs"
    by simp
  finally show "- (2 ^ length bs) \<le> bv_to_nat bs"
    .
next
  fix bs
  from bv_to_nat_upper_range [of "bv_not bs"]
  have "bv_to_nat (bv_not bs) < 2 ^ length bs"
    by simp
  hence "bv_to_nat (bv_not bs) + 1 \<le> 2 ^ length bs"
    by simp
  thus "- (2 ^ length bs) \<le> - bv_to_nat (bv_not bs) + -1"
    by simp
qed

lemma int_bv_int [simp]: "int_to_bv (bv_to_int w) = norm_signed w"
proof (rule bit_list_cases [of w],simp)
  fix xs
  assume [simp]: "w = \<zero>#xs"
  show ?thesis
    apply simp
    apply (subst norm_signed_Cons [of "\<zero>" "xs"])
    apply simp
    using norm_unsigned_result [of xs]
    apply safe
    apply (rule bit_list_cases [of "norm_unsigned xs"])
    apply simp_all
    done
next
  fix xs
  assume [simp]: "w = \<one>#xs"
  show ?thesis
    apply simp
    apply (rule bit_list_induct [of _ xs])
    apply simp
    apply (subst int_to_bv_lt0)
    apply (subgoal_tac "- bv_to_nat (bv_not (\<zero> # bs)) + -1 < 0 + 0")
    apply simp
    apply (rule add_le_less_mono)
    apply simp
    apply (rule order_trans [of _ 0])
    apply simp
    apply (rule zero_le_zpower,simp)
    apply simp
    apply simp
    apply (simp del: bv_to_nat1 bv_to_nat_helper)
    apply simp
    done
qed

lemma bv_int_bv [simp]: "bv_to_int (int_to_bv i) = i"
  by (cases "0 \<le> i",simp_all)

lemma bv_msb_norm [simp]: "bv_msb (norm_signed w) = bv_msb w"
  by (rule bit_list_cases [of w],simp_all add: norm_signed_Cons)

lemma norm_signed_length: "length (norm_signed w) \<le> length w"
  apply (cases w,simp_all)
  apply (subst norm_signed_Cons)
  apply (case_tac "a",simp_all)
  apply (rule rem_initial_length)
  done

lemma norm_signed_equal: "length (norm_signed w) = length w ==> norm_signed w = w"
proof (rule bit_list_cases [of w],simp_all)
  fix xs
  assume "length (norm_signed (\<zero>#xs)) = Suc (length xs)"
  thus "norm_signed (\<zero>#xs) = \<zero>#xs"
    apply (simp add: norm_signed_Cons)
    apply safe
    apply simp_all
    apply (rule norm_unsigned_equal)
    apply assumption
    done
next
  fix xs
  assume "length (norm_signed (\<one>#xs)) = Suc (length xs)"
  thus "norm_signed (\<one>#xs) = \<one>#xs"
    apply (simp add: norm_signed_Cons)
    apply (rule rem_initial_equal)
    apply assumption
    done
qed

lemma bv_extend_norm_signed: "bv_msb w = b ==> bv_extend (length w) b (norm_signed w) = w"
proof (rule bit_list_cases [of w],simp_all)
  fix xs
  show "bv_extend (Suc (length xs)) \<zero> (norm_signed (\<zero>#xs)) = \<zero>#xs"
  proof (simp add: norm_signed_list_def,auto)
    assume "norm_unsigned xs = []"
    hence xx: "rem_initial \<zero> xs = []"
      by (simp add: norm_unsigned_def)
    have "bv_extend (Suc (length xs)) \<zero> (\<zero>#rem_initial \<zero> xs) = \<zero>#xs"
      apply (simp add: bv_extend_def replicate_app_Cons_same)
      apply (fold bv_extend_def)
      apply (rule bv_extend_rem_initial)
      done
    thus "bv_extend (Suc (length xs)) \<zero> [\<zero>] = \<zero>#xs"
      by (simp add: xx)
  next
    show "bv_extend (Suc (length xs)) \<zero> (\<zero>#norm_unsigned xs) = \<zero>#xs"
      apply (simp add: norm_unsigned_def)
      apply (simp add: bv_extend_def replicate_app_Cons_same)
      apply (fold bv_extend_def)
      apply (rule bv_extend_rem_initial)
      done
  qed
next
  fix xs
  show "bv_extend (Suc (length xs)) \<one> (norm_signed (\<one>#xs)) = \<one>#xs"
    apply (simp add: norm_signed_Cons)
    apply (simp add: bv_extend_def replicate_app_Cons_same)
    apply (fold bv_extend_def)
    apply (rule bv_extend_rem_initial)
    done
qed

lemma bv_to_int_qinj:
  assumes one: "bv_to_int xs = bv_to_int ys"
  and     len: "length xs = length ys"
  shows        "xs = ys"
proof -
  from one
  have "int_to_bv (bv_to_int xs) = int_to_bv (bv_to_int ys)"
    by simp
  hence xsys: "norm_signed xs = norm_signed ys"
    by simp
  hence xsys': "bv_msb xs = bv_msb ys"
  proof -
    have "bv_msb xs = bv_msb (norm_signed xs)"
      by simp
    also have "... = bv_msb (norm_signed ys)"
      by (simp add: xsys)
    also have "... = bv_msb ys"
      by simp
    finally show ?thesis .
  qed
  have "xs = bv_extend (length xs) (bv_msb xs) (norm_signed xs)"
    by (simp add: bv_extend_norm_signed)
  also have "... = bv_extend (length ys) (bv_msb ys) (norm_signed ys)"
    by (simp add: xsys xsys' len)
  also have "... = ys"
    by (simp add: bv_extend_norm_signed)
  finally show ?thesis .
qed

lemma [simp]: "norm_signed (int_to_bv w) = int_to_bv w"
  by (simp add: int_to_bv_def)

lemma bv_to_int_msb0: "0 \<le> bv_to_int w1 ==> bv_msb w1 = \<zero>"
  apply (rule bit_list_cases,simp_all)
  apply (subgoal_tac "0 \<le> bv_to_nat (bv_not bs)")
  apply simp_all
  done

lemma bv_to_int_msb1: "bv_to_int w1 < 0 ==> bv_msb w1 = \<one>"
  apply (rule bit_list_cases,simp_all)
  apply (subgoal_tac "0 \<le> bv_to_nat bs")
  apply simp_all
  done

lemma bv_to_int_lower_limit_gt0:
  assumes w0: "0 < bv_to_int w"
  shows       "2 ^ (length (norm_signed w) - 2) \<le> bv_to_int w"
proof -
  from w0
  have "0 \<le> bv_to_int w"
    by simp
  hence [simp]: "bv_msb w = \<zero>"
    by (rule bv_to_int_msb0)
  have "2 ^ (length (norm_signed w) - 2) \<le> bv_to_int (norm_signed w)"
  proof (rule bit_list_cases [of w])
    assume "w = []"
    with w0
    show ?thesis
      by simp
  next
    fix w'
    assume weq: "w = \<zero> # w'"
    thus ?thesis
    proof (simp add: norm_signed_Cons,safe)
      assume "norm_unsigned w' = []"
      with weq and w0
      show False
	by (simp add: norm_empty_bv_to_nat_zero)
    next
      assume w'0: "norm_unsigned w' \<noteq> []"
      have "0 < bv_to_nat w'"
      proof (rule ccontr)
	assume "~ (0 < bv_to_nat w')"
	with bv_to_nat_lower_range [of w']
	have "bv_to_nat w' = 0"
	  by arith
	hence "norm_unsigned w' = []"
	  by (simp add: bv_to_nat_zero_imp_empty)
	with w'0
	show False
	  by simp
      qed
      with bv_to_nat_lower_limit [of w']
      have "2 ^ (length (norm_unsigned w') - 1) \<le> bv_to_nat w'"
	.
      thus "2 ^ (length (norm_unsigned w') - Suc 0) \<le> bv_to_nat w'"
	by simp
    qed
  next
    fix w'
    assume "w = \<one> # w'"
    from w0
    have "bv_msb w = \<zero>"
      by simp
    with prems
    show ?thesis
      by simp
  qed
  also have "...  = bv_to_int w"
    by simp
  finally show ?thesis .
qed

lemma norm_signed_result: "norm_signed w = [] \<or> norm_signed w = [\<one>] \<or> bv_msb (norm_signed w) \<noteq> bv_msb (tl (norm_signed w))"
  apply (rule bit_list_cases [of w],simp_all)
  apply (case_tac "bs",simp_all)
  apply (case_tac "a",simp_all)
  apply (simp add: norm_signed_Cons)
  apply safe
  apply simp
proof -
  fix l
  assume msb: "\<zero> = bv_msb (norm_unsigned l)"
  assume "norm_unsigned l \<noteq> []"
  with norm_unsigned_result [of l]
  have "bv_msb (norm_unsigned l) = \<one>"
    by simp
  with msb
  show False
    by simp
next
  fix xs
  assume p: "\<one> = bv_msb (tl (norm_signed (\<one> # xs)))"
  have "\<one> \<noteq> bv_msb (tl (norm_signed (\<one> # xs)))"
    by (rule bit_list_induct [of _ xs],simp_all)
  with p
  show False
    by simp
qed

lemma bv_to_int_upper_limit_lem1:
  assumes w0: "bv_to_int w < -1"
  shows       "bv_to_int w < - (2 ^ (length (norm_signed w) - 2))"
proof -
  from w0
  have "bv_to_int w < 0"
    by simp
  hence msbw [simp]: "bv_msb w = \<one>"
    by (rule bv_to_int_msb1)
  have "bv_to_int w = bv_to_int (norm_signed w)"
    by simp
  also from norm_signed_result [of w]
  have "... < - (2 ^ (length (norm_signed w) - 2))"
  proof (safe)
    assume "norm_signed w = []"
    hence "bv_to_int (norm_signed w) = 0"
      by simp
    with w0
    show ?thesis
      by simp
  next
    assume "norm_signed w = [\<one>]"
    hence "bv_to_int (norm_signed w) = -1"
      by simp
    with w0
    show ?thesis
      by simp
  next
    assume "bv_msb (norm_signed w) \<noteq> bv_msb (tl (norm_signed w))"
    hence msb_tl: "\<one> \<noteq> bv_msb (tl (norm_signed w))"
      by simp
    show "bv_to_int (norm_signed w) < - (2 ^ (length (norm_signed w) - 2))"
    proof (rule bit_list_cases [of "norm_signed w"])
      assume "norm_signed w = []"
      hence "bv_to_int (norm_signed w) = 0"
	by simp
      with w0
      show ?thesis
	by simp
    next
      fix w'
      assume nw: "norm_signed w = \<zero> # w'"
      from msbw
      have "bv_msb (norm_signed w) = \<one>"
	by simp
      with nw
      show ?thesis
	by simp
    next
      fix w'
      assume weq: "norm_signed w = \<one> # w'"
      show ?thesis
      proof (rule bit_list_cases [of w'])
	assume w'eq: "w' = []"
	from w0
	have "bv_to_int (norm_signed w) < -1"
	  by simp
	with w'eq and weq
	show ?thesis
	  by simp
      next
	fix w''
	assume w'eq: "w' = \<zero> # w''"
	show ?thesis
	  apply (simp add: weq w'eq)
	  apply (subgoal_tac "-bv_to_nat (bv_not w'') + -1 < 0 + 0")
	  apply simp
	  apply (rule add_le_less_mono)
	  apply simp_all
	  done
      next
	fix w''
	assume w'eq: "w' = \<one> # w''"
	with weq and msb_tl
	show ?thesis
	  by simp
      qed
    qed
  qed
  finally show ?thesis .
qed

lemma length_int_to_bv_upper_limit_gt0:
  assumes w0: "0 < i"
  and     wk: "i \<le> 2 ^ (k - 1) - 1"
  shows       "length (int_to_bv i) \<le> k"
proof (rule ccontr)
  from w0 wk
  have k1: "1 < k"
    by (cases "k - 1",simp_all,arith)
  assume "~ length (int_to_bv i) \<le> k"
  hence "k < length (int_to_bv i)"
    by simp
  hence "k \<le> length (int_to_bv i) - 1"
    by arith
  hence a: "k - 1 \<le> length (int_to_bv i) - 2"
    by arith
  have "(2::int) ^ (k - 1) \<le> 2 ^ (length (int_to_bv i) - 2)"
    apply (rule le_imp_power_zle,simp)
    apply (rule a)
    done
  also have "... \<le> i"
  proof -
    have "2 ^ (length (norm_signed (int_to_bv i)) - 2) \<le> bv_to_int (int_to_bv i)"
    proof (rule bv_to_int_lower_limit_gt0)
      from w0
      show "0 < bv_to_int (int_to_bv i)"
	by simp
    qed
    thus ?thesis
      by simp
  qed
  finally have "2 ^ (k - 1) \<le> i" .
  with wk
  show False
    by simp
qed

lemma pos_length_pos:
  assumes i0: "0 < bv_to_int w"
  shows       "0 < length w"
proof -
  from norm_signed_result [of w]
  have "0 < length (norm_signed w)"
  proof (auto)
    assume ii: "norm_signed w = []"
    have "bv_to_int (norm_signed w) = 0"
      by (subst ii,simp)
    hence "bv_to_int w = 0"
      by simp
    with i0
    show False
      by simp
  next
    assume ii: "norm_signed w = []"
    assume jj: "bv_msb w \<noteq> \<zero>"
    have "\<zero> = bv_msb (norm_signed w)"
      by (subst ii,simp)
    also have "... \<noteq> \<zero>"
      by (simp add: jj)
    finally show False by simp
  qed
  also have "... \<le> length w"
    by (rule norm_signed_length)
  finally show ?thesis
    .
qed

lemma neg_length_pos:
  assumes i0: "bv_to_int w < -1"
  shows       "0 < length w"
proof -
  from norm_signed_result [of w]
  have "0 < length (norm_signed w)"
  proof (auto)
    assume ii: "norm_signed w = []"
    have "bv_to_int (norm_signed w) = 0"
      by (subst ii,simp)
    hence "bv_to_int w = 0"
      by simp
    with i0
    show False
      by simp
  next
    assume ii: "norm_signed w = []"
    assume jj: "bv_msb w \<noteq> \<zero>"
    have "\<zero> = bv_msb (norm_signed w)"
      by (subst ii,simp)
    also have "... \<noteq> \<zero>"
      by (simp add: jj)
    finally show False by simp
  qed
  also have "... \<le> length w"
    by (rule norm_signed_length)
  finally show ?thesis
    .
qed

lemma length_int_to_bv_lower_limit_gt0:
  assumes wk: "2 ^ (k - 1) \<le> i"
  shows       "k < length (int_to_bv i)"
proof (rule ccontr)
  have "0 < (2::int) ^ (k - 1)"
    by (rule zero_less_zpower,simp)
  also have "... \<le> i"
    by (rule wk)
  finally have i0: "0 < i"
    .
  have lii0: "0 < length (int_to_bv i)"
    apply (rule pos_length_pos)
    apply (simp,rule i0)
    done
  assume "~ k < length (int_to_bv i)"
  hence "length (int_to_bv i) \<le> k"
    by simp
  with lii0
  have a: "length (int_to_bv i) - 1 \<le> k - 1"
    by arith
  have "i < 2 ^ (length (int_to_bv i) - 1)"
  proof -
    have "i = bv_to_int (int_to_bv i)"
      by simp
    also have "... < 2 ^ (length (int_to_bv i) - 1)"
      by (rule bv_to_int_upper_range)
    finally show ?thesis .
  qed
  also have "(2::int) ^ (length (int_to_bv i) - 1) \<le> 2 ^ (k - 1)"
    apply (rule le_imp_power_zle,simp)
    apply (rule a)
    done
  finally have "i < 2 ^ (k - 1)" .
  with wk
  show False
    by simp
qed

lemma length_int_to_bv_upper_limit_lem1:
  assumes w1: "i < -1"
  and     wk: "- (2 ^ (k - 1)) \<le> i"
  shows       "length (int_to_bv i) \<le> k"
proof (rule ccontr)
  from w1 wk
  have k1: "1 < k"
    by (cases "k - 1",simp_all,arith)
  assume "~ length (int_to_bv i) \<le> k"
  hence "k < length (int_to_bv i)"
    by simp
  hence "k \<le> length (int_to_bv i) - 1"
    by arith
  hence a: "k - 1 \<le> length (int_to_bv i) - 2"
    by arith
  have "i < - (2 ^ (length (int_to_bv i) - 2))"
  proof -
    have "i = bv_to_int (int_to_bv i)"
      by simp
    also have "... < - (2 ^ (length (norm_signed (int_to_bv i)) - 2))"
      by (rule bv_to_int_upper_limit_lem1,simp,rule w1)
    finally show ?thesis by simp
  qed
  also have "... \<le> -(2 ^ (k - 1))"
  proof -
    have "(2::int) ^ (k - 1) \<le> 2 ^ (length (int_to_bv i) - 2)"
      apply (rule le_imp_power_zle,simp)
      apply (rule a)
      done
    thus ?thesis
      by simp
  qed
  finally have "i < -(2 ^ (k - 1))" .
  with wk
  show False
    by simp
qed

lemma length_int_to_bv_lower_limit_lem1:
  assumes wk: "i < -(2 ^ (k - 1))"
  shows       "k < length (int_to_bv i)"
proof (rule ccontr)
  from wk
  have "i \<le> -(2 ^ (k - 1)) - 1"
    by simp
  also have "... < -1"
  proof -
    have "0 < (2::int) ^ (k - 1)"
      by (rule zero_less_zpower,simp)
    hence "-((2::int) ^ (k - 1)) < 0"
      by simp
    thus ?thesis by simp
  qed
  finally have i1: "i < -1" .
  have lii0: "0 < length (int_to_bv i)"
    apply (rule neg_length_pos)
    apply (simp,rule i1)
    done
  assume "~ k < length (int_to_bv i)"
  hence "length (int_to_bv i) \<le> k"
    by simp
  with lii0
  have a: "length (int_to_bv i) - 1 \<le> k - 1"
    by arith
  have "(2::int) ^ (length (int_to_bv i) - 1) \<le> 2 ^ (k - 1)"
    apply (rule le_imp_power_zle,simp)
    apply (rule a)
    done
  hence "-((2::int) ^ (k - 1)) \<le> - (2 ^ (length (int_to_bv i) - 1))"
    by simp
  also have "... \<le> i"
  proof -
    have "- (2 ^ (length (int_to_bv i) - 1)) \<le> bv_to_int (int_to_bv i)"
      by (rule bv_to_int_lower_range)
    also have "... = i"
      by simp
    finally show ?thesis .
  qed
  finally have "-(2 ^ (k - 1)) \<le> i" .
  with wk
  show False
    by simp
qed

section {* Signed Arithmetic Operations *}

subsection {* Conversion from unsigned to signed *}

constdefs
  utos :: "bit list => bit list"
  "utos w == norm_signed (\<zero> # w)"

lemma [simp]: "utos (norm_unsigned w) = utos w"
  by (simp add: utos_def norm_signed_Cons)

lemma [simp]: "norm_signed (utos w) = utos w"
  by (simp add: utos_def)

lemma utos_length: "length (utos w) \<le> Suc (length w)"
  by (simp add: utos_def norm_signed_Cons)

lemma bv_to_int_utos: "bv_to_int (utos w) = bv_to_nat w"
proof (simp add: utos_def norm_signed_Cons,safe)
  assume "norm_unsigned w = []"
  hence "bv_to_nat (norm_unsigned w) = 0"
    by simp
  thus "bv_to_nat w = 0"
    by simp
qed

subsection {* Unary minus *}

constdefs
  bv_uminus :: "bit list => bit list"
  "bv_uminus w == int_to_bv (- bv_to_int w)"

lemma [simp]: "bv_uminus (norm_signed w) = bv_uminus w"
  by (simp add: bv_uminus_def)

lemma [simp]: "norm_signed (bv_uminus w) = bv_uminus w"
  by (simp add: bv_uminus_def)

lemma bv_uminus_length: "length (bv_uminus w) \<le> Suc (length w)"
proof -
  have "1 < -bv_to_int w \<or> -bv_to_int w = 1 \<or> -bv_to_int w = 0 \<or> -bv_to_int w = -1 \<or> -bv_to_int w < -1"
    by arith
  thus ?thesis
  proof safe
    assume p: "1 < - bv_to_int w"
    have lw: "0 < length w"
      apply (rule neg_length_pos)
      using p
      apply simp
      done
    show ?thesis
    proof (simp add: bv_uminus_def,rule length_int_to_bv_upper_limit_gt0,simp_all)
      from prems
      show "bv_to_int w < 0"
	by simp
    next
      have "-(2^(length w - 1)) \<le> bv_to_int w"
	by (rule bv_to_int_lower_range)
      hence "- bv_to_int w \<le> 2^(length w - 1)"
	by simp
      also from lw have "... < 2 ^ length w"
	by simp
      finally show "- bv_to_int w < 2 ^ length w"
	by simp
    qed
  next
    assume p: "- bv_to_int w = 1"
    hence lw: "0 < length w"
      by (cases w,simp_all)
    from p
    show ?thesis
      apply (simp add: bv_uminus_def)
      using lw
      apply (simp (no_asm) add: nat_to_bv_non0)
      done
  next
    assume "- bv_to_int w = 0"
    thus ?thesis
      by (simp add: bv_uminus_def)
  next
    assume p: "- bv_to_int w = -1"
    thus ?thesis
      by (simp add: bv_uminus_def)
  next
    assume p: "- bv_to_int w < -1"
    show ?thesis
      apply (simp add: bv_uminus_def)
      apply (rule length_int_to_bv_upper_limit_lem1)
      apply (rule p)
      apply simp
    proof -
      have "bv_to_int w < 2 ^ (length w - 1)"
	by (rule bv_to_int_upper_range)
      also have "... \<le> 2 ^ length w"
	by (rule le_imp_power_zle,simp_all)
      finally show "bv_to_int w \<le> 2 ^ length w"
	by simp
    qed
  qed
qed

lemma bv_uminus_length_utos: "length (bv_uminus (utos w)) \<le> Suc (length w)"
proof -
  have "-bv_to_int (utos w) = 0 \<or> -bv_to_int (utos w) = -1 \<or> -bv_to_int (utos w) < -1"
    apply (simp add: bv_to_int_utos)
    apply (cut_tac bv_to_nat_lower_range [of w])
    by arith
  thus ?thesis
  proof safe
    assume "-bv_to_int (utos w) = 0"
    thus ?thesis
      by (simp add: bv_uminus_def)
  next
    assume "-bv_to_int (utos w) = -1"
    thus ?thesis
      by (simp add: bv_uminus_def)
  next
    assume p: "-bv_to_int (utos w) < -1"
    show ?thesis
      apply (simp add: bv_uminus_def)
      apply (rule length_int_to_bv_upper_limit_lem1)
      apply (rule p)
      apply (simp add: bv_to_int_utos)
      using bv_to_nat_upper_range [of w]
      apply simp
      done
  qed
qed

constdefs
  bv_sadd :: "[bit list, bit list ] => bit list"
  "bv_sadd w1 w2 == int_to_bv (bv_to_int w1 + bv_to_int w2)"

lemma [simp]: "bv_sadd (norm_signed w1) w2 = bv_sadd w1 w2"
  by (simp add: bv_sadd_def)

lemma [simp]: "bv_sadd w1 (norm_signed w2) = bv_sadd w1 w2"
  by (simp add: bv_sadd_def)

lemma [simp]: "norm_signed (bv_sadd w1 w2) = bv_sadd w1 w2"
  by (simp add: bv_sadd_def)

lemma adder_helper:
  assumes lw: "0 < max (length w1) (length w2)"
  shows   "((2::int) ^ (length w1 - 1)) + (2 ^ (length w2 - 1)) \<le> 2 ^ max (length w1) (length w2)"
proof -
  have "((2::int) ^ (length w1 - 1)) + (2 ^ (length w2 - 1)) \<le> 2 ^ (max (length w1) (length w2) - 1) + 2 ^ (max (length w1) (length w2) - 1)"
    apply (cases "length w1 \<le> length w2")
    apply (auto simp add: max_def)
    apply arith
    apply arith
    done
  also have "... = 2 ^ max (length w1) (length w2)"
  proof -
    from lw
    show ?thesis
      apply simp
      apply (subst power_Suc [symmetric])
      apply (simp del: power.simps)
      done
  qed
  finally show ?thesis .
qed

lemma bv_sadd_length: "length (bv_sadd w1 w2) \<le> Suc (max (length w1) (length w2))"
proof -
  let ?Q = "bv_to_int w1 + bv_to_int w2"

  have helper: "?Q \<noteq> 0 ==> 0 < max (length w1) (length w2)"
  proof -
    assume p: "?Q \<noteq> 0"
    show "0 < max (length w1) (length w2)"
    proof (simp add: less_max_iff_disj,rule)
      assume [simp]: "w1 = []"
      show "w2 \<noteq> []"
      proof (rule ccontr,simp)
	assume [simp]: "w2 = []"
	from p
	show False
	  by simp
      qed
    qed
  qed

  have "0 < ?Q \<or> ?Q = 0 \<or> ?Q = -1 \<or> ?Q < -1"
    by arith
  thus ?thesis
  proof safe
    assume "?Q = 0"
    thus ?thesis
      by (simp add: bv_sadd_def)
  next
    assume "?Q = -1"
    thus ?thesis
      by (simp add: bv_sadd_def)
  next
    assume p: "0 < ?Q"
    show ?thesis
      apply (simp add: bv_sadd_def)
      apply (rule length_int_to_bv_upper_limit_gt0)
      apply (rule p)
    proof simp
      from bv_to_int_upper_range [of w2]
      have "bv_to_int w2 \<le> 2 ^ (length w2 - 1)"
	by simp
      with bv_to_int_upper_range [of w1]
      have "bv_to_int w1 + bv_to_int w2 < (2 ^ (length w1 - 1)) + (2 ^ (length w2 - 1))"
	by (rule zadd_zless_mono)
      also have "... \<le> 2 ^ max (length w1) (length w2)"
	apply (rule adder_helper)
	apply (rule helper)
	using p
	apply simp
	done
      finally show "?Q < 2 ^ max (length w1) (length w2)"
	.
    qed
  next
    assume p: "?Q < -1"
    show ?thesis
      apply (simp add: bv_sadd_def)
      apply (rule length_int_to_bv_upper_limit_lem1,simp_all)
      apply (rule p)
    proof -
      have "(2 ^ (length w1 - 1)) + 2 ^ (length w2 - 1) \<le> (2::int) ^ max (length w1) (length w2)"
	apply (rule adder_helper)
	apply (rule helper)
	using p
	apply simp
	done
      hence "-((2::int) ^ max (length w1) (length w2)) \<le> - (2 ^ (length w1 - 1)) + -(2 ^ (length w2 - 1))"
	by simp
      also have "- (2 ^ (length w1 - 1)) + -(2 ^ (length w2 - 1)) \<le> ?Q"
	apply (rule add_mono)
	apply (rule bv_to_int_lower_range [of w1])
	apply (rule bv_to_int_lower_range [of w2])
	done
      finally show "- (2^max (length w1) (length w2)) \<le> ?Q" .
    qed
  qed
qed

constdefs
  bv_sub :: "[bit list, bit list] => bit list"
  "bv_sub w1 w2 == bv_sadd w1 (bv_uminus w2)"

lemma [simp]: "bv_sub (norm_signed w1) w2 = bv_sub w1 w2"
  by (simp add: bv_sub_def)

lemma [simp]: "bv_sub w1 (norm_signed w2) = bv_sub w1 w2"
  by (simp add: bv_sub_def)

lemma [simp]: "norm_signed (bv_sub w1 w2) = bv_sub w1 w2"
  by (simp add: bv_sub_def)

lemma bv_sub_length: "length (bv_sub w1 w2) \<le> Suc (max (length w1) (length w2))"
proof (cases "bv_to_int w2 = 0")
  assume p: "bv_to_int w2 = 0"
  show ?thesis
  proof (simp add: bv_sub_def bv_sadd_def bv_uminus_def p)
    have "length (norm_signed w1) \<le> length w1"
      by (rule norm_signed_length)
    also have "... \<le> max (length w1) (length w2)"
      by (rule le_maxI1)
    also have "... \<le> Suc (max (length w1) (length w2))"
      by arith
    finally show "length (norm_signed w1) \<le> Suc (max (length w1) (length w2))"
      .
  qed
next
  assume "bv_to_int w2 \<noteq> 0"
  hence "0 < length w2"
    by (cases w2,simp_all)
  hence lmw: "0 < max (length w1) (length w2)"
    by arith

  let ?Q = "bv_to_int w1 - bv_to_int w2"

  have "0 < ?Q \<or> ?Q = 0 \<or> ?Q = -1 \<or> ?Q < -1"
    by arith
  thus ?thesis
  proof safe
    assume "?Q = 0"
    thus ?thesis
      by (simp add: bv_sub_def bv_sadd_def bv_uminus_def)
  next
    assume "?Q = -1"
    thus ?thesis
      by (simp add: bv_sub_def bv_sadd_def bv_uminus_def)
  next
    assume p: "0 < ?Q"
    show ?thesis
      apply (simp add: bv_sub_def bv_sadd_def bv_uminus_def)
      apply (rule length_int_to_bv_upper_limit_gt0)
      apply (rule p)
    proof simp
      from bv_to_int_lower_range [of w2]
      have v2: "- bv_to_int w2 \<le> 2 ^ (length w2 - 1)"
	by simp
      have "bv_to_int w1 + - bv_to_int w2 < (2 ^ (length w1 - 1)) + (2 ^ (length w2 - 1))"
	apply (rule zadd_zless_mono)
	apply (rule bv_to_int_upper_range [of w1])
	apply (rule v2)
	done
      also have "... \<le> 2 ^ max (length w1) (length w2)"
	apply (rule adder_helper)
	apply (rule lmw)
	done
      finally show "?Q < 2 ^ max (length w1) (length w2)"
	by simp
    qed
  next
    assume p: "?Q < -1"
    show ?thesis
      apply (simp add: bv_sub_def bv_sadd_def bv_uminus_def)
      apply (rule length_int_to_bv_upper_limit_lem1)
      apply (rule p)
    proof simp
      have "(2 ^ (length w1 - 1)) + 2 ^ (length w2 - 1) \<le> (2::int) ^ max (length w1) (length w2)"
	apply (rule adder_helper)
	apply (rule lmw)
	done
      hence "-((2::int) ^ max (length w1) (length w2)) \<le> - (2 ^ (length w1 - 1)) + -(2 ^ (length w2 - 1))"
	by simp
      also have "- (2 ^ (length w1 - 1)) + -(2 ^ (length w2 - 1)) \<le> bv_to_int w1 + -bv_to_int w2"
	apply (rule add_mono)
	apply (rule bv_to_int_lower_range [of w1])
	using bv_to_int_upper_range [of w2]
	apply simp
	done
      finally show "- (2^max (length w1) (length w2)) \<le> ?Q"
	by simp
    qed
  qed
qed

constdefs
  bv_smult :: "[bit list, bit list] => bit list"
  "bv_smult w1 w2 == int_to_bv (bv_to_int w1 * bv_to_int w2)"

lemma [simp]: "bv_smult (norm_signed w1) w2 = bv_smult w1 w2"
  by (simp add: bv_smult_def)

lemma [simp]: "bv_smult w1 (norm_signed w2) = bv_smult w1 w2"
  by (simp add: bv_smult_def)

lemma [simp]: "norm_signed (bv_smult w1 w2) = bv_smult w1 w2"
  by (simp add: bv_smult_def)

lemma bv_smult_length: "length (bv_smult w1 w2) \<le> length w1 + length w2"
proof -
  let ?Q = "bv_to_int w1 * bv_to_int w2"

  have lmw: "?Q \<noteq> 0 ==> 0 < length w1 \<and> 0 < length w2"
    by auto

  have "0 < ?Q \<or> ?Q = 0 \<or> ?Q = -1 \<or> ?Q < -1"
    by arith
  thus ?thesis
  proof (safe dest!: iffD1 [OF mult_eq_0_iff])
    assume "bv_to_int w1 = 0"
    thus ?thesis
      by (simp add: bv_smult_def)
  next
    assume "bv_to_int w2 = 0"
    thus ?thesis
      by (simp add: bv_smult_def)
  next
    assume p: "?Q = -1"
    show ?thesis
      apply (simp add: bv_smult_def p)
      apply (cut_tac lmw)
      apply arith
      using p
      apply simp
      done
  next
    assume p: "0 < ?Q"
    thus ?thesis
    proof (simp add: zero_less_mult_iff,safe)
      assume bi1: "0 < bv_to_int w1"
      assume bi2: "0 < bv_to_int w2"
      show ?thesis
	apply (simp add: bv_smult_def)
	apply (rule length_int_to_bv_upper_limit_gt0)
	apply (rule p)
      proof simp
	have "?Q < 2 ^ (length w1 - 1) * 2 ^ (length w2 - 1)"
	  apply (rule mult_strict_mono)
	  apply (rule bv_to_int_upper_range)
	  apply (rule bv_to_int_upper_range)
	  apply (rule zero_less_zpower)
	  apply simp
	  using bi2
	  apply simp
	  done
	also have "... \<le> 2 ^ (length w1 + length w2 - Suc 0)"
	  apply simp
	  apply (subst zpower_zadd_distrib [symmetric])
	  apply simp
	  apply arith
	  done
	finally show "?Q < 2 ^ (length w1 + length w2 - Suc 0)"
	  .
      qed
    next
      assume bi1: "bv_to_int w1 < 0"
      assume bi2: "bv_to_int w2 < 0"
      show ?thesis
	apply (simp add: bv_smult_def)
	apply (rule length_int_to_bv_upper_limit_gt0)
	apply (rule p)
      proof simp
	have "-bv_to_int w1 * -bv_to_int w2 \<le> 2 ^ (length w1 - 1) * 2 ^(length w2 - 1)"
	  apply (rule mult_mono)
	  using bv_to_int_lower_range [of w1]
	  apply simp
	  using bv_to_int_lower_range [of w2]
	  apply simp
	  apply (rule zero_le_zpower,simp)
	  using bi2
	  apply simp
	  done
	hence "?Q \<le> 2 ^ (length w1 - 1) * 2 ^(length w2 - 1)"
	  by simp
	also have "... < 2 ^ (length w1 + length w2 - Suc 0)"
	  apply simp
	  apply (subst zpower_zadd_distrib [symmetric])
	  apply simp
	  apply (cut_tac lmw)
	  apply arith
	  apply (cut_tac p)
	  apply arith
	  done
	finally show "?Q < 2 ^ (length w1 + length w2 - Suc 0)" .
      qed
    qed
  next
    assume p: "?Q < -1"
    show ?thesis
      apply (subst bv_smult_def)
      apply (rule length_int_to_bv_upper_limit_lem1)
      apply (rule p)
    proof simp
      have "(2::int) ^ (length w1 - 1) * 2 ^(length w2 - 1) \<le> 2 ^ (length w1 + length w2 - Suc 0)"
	apply simp
	apply (subst zpower_zadd_distrib [symmetric])
	apply simp
	apply (cut_tac lmw)
	apply arith
	apply (cut_tac p)
	apply arith
	done
      hence "-((2::int) ^ (length w1 + length w2 - Suc 0)) \<le> -(2^(length w1 - 1) * 2 ^ (length w2 - 1))"
	by simp
      also have "... \<le> ?Q"
      proof -
	from p
	have q: "bv_to_int w1 * bv_to_int w2 < 0"
	  by simp
	thus ?thesis
	proof (simp add: mult_less_0_iff,safe)
	  assume bi1: "0 < bv_to_int w1"
	  assume bi2: "bv_to_int w2 < 0"
	  have "-bv_to_int w2 * bv_to_int w1 \<le> ((2::int)^(length w2 - 1)) * (2 ^ (length w1 - 1))"
	    apply (rule mult_mono)
	    using bv_to_int_lower_range [of w2]
	    apply simp
	    using bv_to_int_upper_range [of w1]
	    apply simp
	    apply (rule zero_le_zpower,simp)
	    using bi1
	    apply simp
	    done
	  hence "-?Q \<le> ((2::int)^(length w1 - 1)) * (2 ^ (length w2 - 1))"
	    by (simp add: zmult_ac)
	  thus "-(((2::int)^(length w1 - Suc 0)) * (2 ^ (length w2 - Suc 0))) \<le> ?Q"
	    by simp
	next
	  assume bi1: "bv_to_int w1 < 0"
	  assume bi2: "0 < bv_to_int w2"
	  have "-bv_to_int w1 * bv_to_int w2 \<le> ((2::int)^(length w1 - 1)) * (2 ^ (length w2 - 1))"
	    apply (rule mult_mono)
	    using bv_to_int_lower_range [of w1]
	    apply simp
	    using bv_to_int_upper_range [of w2]
	    apply simp
	    apply (rule zero_le_zpower,simp)
	    using bi2
	    apply simp
	    done
	  hence "-?Q \<le> ((2::int)^(length w1 - 1)) * (2 ^ (length w2 - 1))"
	    by (simp add: zmult_ac)
	  thus "-(((2::int)^(length w1 - Suc 0)) * (2 ^ (length w2 - Suc 0))) \<le> ?Q"
	    by simp
	qed
      qed
      finally show "-(2 ^ (length w1 + length w2 - Suc 0)) \<le> ?Q"
	.
    qed
  qed
qed

lemma bv_msb_one: "bv_msb w = \<one> ==> 0 < bv_to_nat w"
  apply (cases w,simp_all)
  apply (subgoal_tac "0 + 0 < 2 ^ length list + bv_to_nat list")
  apply simp
  apply (rule add_less_le_mono)
  apply (rule zero_less_zpower)
  apply simp_all
  done

lemma bv_smult_length_utos: "length (bv_smult (utos w1) w2) \<le> length w1 + length w2"
proof -
  let ?Q = "bv_to_int (utos w1) * bv_to_int w2"

  have lmw: "?Q \<noteq> 0 ==> 0 < length (utos w1) \<and> 0 < length w2"
    by auto

  have "0 < ?Q \<or> ?Q = 0 \<or> ?Q = -1 \<or> ?Q < -1"
    by arith
  thus ?thesis
  proof (safe dest!: iffD1 [OF mult_eq_0_iff])
    assume "bv_to_int (utos w1) = 0"
    thus ?thesis
      by (simp add: bv_smult_def)
  next
    assume "bv_to_int w2 = 0"
    thus ?thesis
      by (simp add: bv_smult_def)
  next
    assume p: "0 < ?Q"
    thus ?thesis
    proof (simp add: zero_less_mult_iff,safe)
      assume biw2: "0 < bv_to_int w2"
      show ?thesis
	apply (simp add: bv_smult_def)
	apply (rule length_int_to_bv_upper_limit_gt0)
	apply (rule p)
      proof simp
	have "?Q < 2 ^ length w1 * 2 ^ (length w2 - 1)"
	  apply (rule mult_strict_mono)
	  apply (simp add: bv_to_int_utos)
	  apply (rule bv_to_nat_upper_range)
	  apply (rule bv_to_int_upper_range)
	  apply (rule zero_less_zpower,simp)
	  using biw2
	  apply simp
	  done
	also have "... \<le> 2 ^ (length w1 + length w2 - Suc 0)"
 	  apply simp
	  apply (subst zpower_zadd_distrib [symmetric])
	  apply simp
	  apply (cut_tac lmw)
	  apply arith
	  using p
	  apply auto
	  done
	finally show "?Q < 2 ^ (length w1 + length w2 - Suc 0)"
	  .
      qed
    next
      assume "bv_to_int (utos w1) < 0"
      thus ?thesis
	apply (simp add: bv_to_int_utos)
	using bv_to_nat_lower_range [of w1]
	apply simp
	done
    qed
  next
    assume p: "?Q = -1"
    thus ?thesis
      apply (simp add: bv_smult_def)
      apply (cut_tac lmw)
      apply arith
      apply simp
      done
  next
    assume p: "?Q < -1"
    show ?thesis
      apply (subst bv_smult_def)
      apply (rule length_int_to_bv_upper_limit_lem1)
      apply (rule p)
    proof simp
      have "(2::int) ^ length w1 * 2 ^(length w2 - 1) \<le> 2 ^ (length w1 + length w2 - Suc 0)"
	apply simp
	apply (subst zpower_zadd_distrib [symmetric])
	apply simp
	apply (cut_tac lmw)
	apply arith
	apply (cut_tac p)
	apply arith
	done
      hence "-((2::int) ^ (length w1 + length w2 - Suc 0)) \<le> -(2^ length w1 * 2 ^ (length w2 - 1))"
	by simp
      also have "... \<le> ?Q"
      proof -
	from p
	have q: "bv_to_int (utos w1) * bv_to_int w2 < 0"
	  by simp
	thus ?thesis
	proof (simp add: mult_less_0_iff,safe)
	  assume bi1: "0 < bv_to_int (utos w1)"
	  assume bi2: "bv_to_int w2 < 0"
	  have "-bv_to_int w2 * bv_to_int (utos w1) \<le> ((2::int)^(length w2 - 1)) * (2 ^ length w1)"
	    apply (rule mult_mono)
	    using bv_to_int_lower_range [of w2]
	    apply simp
	    apply (simp add: bv_to_int_utos)
	    using bv_to_nat_upper_range [of w1]
	    apply simp
	    apply (rule zero_le_zpower,simp)
	    using bi1
	    apply simp
	    done
	  hence "-?Q \<le> ((2::int)^length w1) * (2 ^ (length w2 - 1))"
	    by (simp add: zmult_ac)
	  thus "-(((2::int)^length w1) * (2 ^ (length w2 - Suc 0))) \<le> ?Q"
	    by simp
	next
	  assume bi1: "bv_to_int (utos w1) < 0"
	  thus "-(((2::int)^length w1) * (2 ^ (length w2 - Suc 0))) \<le> ?Q"
	    apply (simp add: bv_to_int_utos)
	    using bv_to_nat_lower_range [of w1]
	    apply simp
	    done
	qed
      qed
      finally show "-(2 ^ (length w1 + length w2 - Suc 0)) \<le> ?Q"
	.
    qed
  qed
qed

lemma bv_smult_sym: "bv_smult w1 w2 = bv_smult w2 w1"
  by (simp add: bv_smult_def zmult_ac)

section {* Structural operations *}

constdefs
  bv_select :: "[bit list,nat] => bit"
  "bv_select w i == w ! (length w - 1 - i)"
  bv_chop :: "[bit list,nat] => bit list * bit list"
  "bv_chop w i == let len = length w in (take (len - i) w,drop (len - i) w)"
  bv_slice :: "[bit list,nat*nat] => bit list"
  "bv_slice w == \<lambda>(b,e). fst (bv_chop (snd (bv_chop w (b+1))) e)"

lemma bv_select_rev:
  assumes notnull: "n < length w"
  shows            "bv_select w n = rev w ! n"
proof -
  have "\<forall>n. n < length w --> bv_select w n = rev w ! n"
  proof (rule length_induct [of _ w],auto simp add: bv_select_def)
    fix xs :: "bit list"
    fix n
    assume ind: "\<forall>ys::bit list. length ys < length xs --> (\<forall>n. n < length ys --> ys ! (length ys - Suc n) = rev ys ! n)"
    assume notx: "n < length xs"
    show "xs ! (length xs - Suc n) = rev xs ! n"
    proof (cases xs)
      assume "xs = []"
      with notx
      show ?thesis
	by simp
    next
      fix y ys
      assume [simp]: "xs = y # ys"
      show ?thesis
      proof (auto simp add: nth_append)
	assume noty: "n < length ys"
	from spec [OF ind,of ys]
	have "\<forall>n. n < length ys --> ys ! (length ys - Suc n) = rev ys ! n"
	  by simp
	hence "n < length ys --> ys ! (length ys - Suc n) = rev ys ! n"
	  ..
	hence "ys ! (length ys - Suc n) = rev ys ! n"
	  ..
	thus "(y # ys) ! (length ys - n) = rev ys ! n"
	  by (simp add: nth_Cons' noty not_less_iff_le [symmetric])
      next
	assume "~ n < length ys"
	hence x: "length ys \<le> n"
	  by simp
	from notx
	have "n < Suc (length ys)"
	  by simp
	hence "n \<le> length ys"
	  by simp
	with x
	have "length ys = n"
	  by simp
	thus "y = [y] ! (n - length ys)"
	  by simp
      qed
    qed
  qed
  hence "n < length w --> bv_select w n = rev w ! n"
    ..
  thus ?thesis
    ..
qed

lemma bv_chop_append: "bv_chop (w1 @ w2) (length w2) = (w1,w2)"
  by (simp add: bv_chop_def Let_def)

lemma append_bv_chop_id: "fst (bv_chop w l) @ snd (bv_chop w l) = w"
  by (simp add: bv_chop_def Let_def)

lemma bv_chop_length_fst [simp]: "length (fst (bv_chop w i)) = length w - i"
  by (simp add: bv_chop_def Let_def,arith)

lemma bv_chop_length_snd [simp]: "length (snd (bv_chop w i)) = min i (length w)"
  by (simp add: bv_chop_def Let_def,arith)

lemma bv_slice_length [simp]: "[| j \<le> i; i < length w |] ==> length (bv_slice w (i,j)) = i - j + 1"
  by (auto simp add: bv_slice_def,arith)

constdefs
  length_nat :: "int => nat"
  "length_nat x == LEAST n. x < 2 ^ n"

lemma length_nat: "length (nat_to_bv n) = length_nat n"
  apply (simp add: length_nat_def)
  apply (rule Least_equality [symmetric])
  prefer 2
  apply (rule length_nat_to_bv_upper_limit)
  apply arith
  apply (rule ccontr)
proof -
  assume "~ n < 2 ^ length (nat_to_bv n)"
  hence "2 ^ length (nat_to_bv n) \<le> n"
    by simp
  hence "length (nat_to_bv n) < length (nat_to_bv n)"
    by (rule length_nat_to_bv_lower_limit)
  thus False
    by simp
qed

lemma length_nat_0 [simp]: "length_nat 0 = 0"
  by (simp add: length_nat_def Least_equality)

lemma length_nat_non0:
  assumes n0: "0 < n"
  shows       "length_nat n = Suc (length_nat (n div 2))"
  apply (simp add: length_nat [symmetric])
  apply (subst nat_to_bv_non0 [of n])
  apply (simp_all add: n0)
  done

constdefs
  length_int :: "int => nat"
  "length_int x == if 0 < x then Suc (length_nat x) else if x = 0 then 0 else Suc (length_nat (-x - 1))"

lemma length_int: "length (int_to_bv i) = length_int i"
proof (cases "0 < i")
  assume i0: "0 < i"
  hence "length (int_to_bv i) = length (norm_signed (\<zero> # norm_unsigned (nat_to_bv i)))"
    by simp
  also from norm_unsigned_result [of "nat_to_bv i"]
  have "... = Suc (length_nat i)"
    apply safe
    apply simp
    apply (drule norm_empty_bv_to_nat_zero)
    using prems
    apply simp
    apply (cases "norm_unsigned (nat_to_bv i)")
    apply (drule norm_empty_bv_to_nat_zero [of "nat_to_bv i"])
    using prems
    apply simp
    apply simp
    using prems
    apply (simp add: length_nat [symmetric])
    done
  finally show ?thesis
    using i0
    by (simp add: length_int_def)
next
  assume "~ 0 < i"
  hence i0: "i \<le> 0"
    by simp
  show ?thesis
  proof (cases "i = 0")
    assume "i = 0"
    thus ?thesis
      by (simp add: length_int_def)
  next
    assume "i \<noteq> 0"
    with i0
    have i0: "i < 0"
      by simp
    hence "length (int_to_bv i) = length (norm_signed (\<one> # bv_not (norm_unsigned (nat_to_bv (- i - 1)))))"
      by (simp add: int_to_bv_def)
    also from norm_unsigned_result [of "nat_to_bv (- i - 1)"]
    have "... = Suc (length_nat (- i - 1))"
      apply safe
      apply simp
      apply (drule norm_empty_bv_to_nat_zero [of "nat_to_bv (-i - 1)"])
      using prems
      apply simp
      apply (cases "- i - 1 = 0")
      apply simp
      apply (simp add: length_nat [symmetric])
      apply (cases "norm_unsigned (nat_to_bv (- i - 1))")
      apply simp
      apply simp
      using prems
      apply (simp add: length_nat [symmetric])
      done
    finally
    show ?thesis
      using i0
      by (simp add: length_int_def)
  qed
qed

lemma length_int_0 [simp]: "length_int 0 = 0"
  by (simp add: length_int_def)

lemma length_int_gt0: "0 < i ==> length_int i = Suc (length_nat i)"
  by (simp add: length_int_def)

lemma length_int_lt0: "i < 0 ==> length_int i = Suc (length_nat (- i - 1))"
  by (simp add: length_int_def)

lemma bv_chopI: "[| w = w1 @ w2 ; i = length w2 |] ==> bv_chop w i = (w1,w2)"
  by (simp add: bv_chop_def Let_def)

lemma bv_sliceI: "[| j \<le> i ; i < length w ; w = w1 @ w2 @ w3 ; Suc i = length w2 + j ; j = length w3  |] ==> bv_slice w (i,j) = w2"
  apply (simp add: bv_slice_def)
  apply (subst bv_chopI [of "w1 @ w2 @ w3" w1 "w2 @ w3"])
  apply simp
  apply simp
  apply simp
  apply (subst bv_chopI [of "w2 @ w3" w2 w3],simp_all)
  done

lemma bv_slice_bv_slice:
  assumes ki: "k \<le> i"
  and     ij: "i \<le> j"
  and     jl: "j \<le> l"
  and     lw: "l < length w"
  shows       "bv_slice w (j,i) = bv_slice (bv_slice w (l,k)) (j-k,i-k)"
proof -
  def w1  == "fst (bv_chop w (Suc l))"
  def w2  == "fst (bv_chop (snd (bv_chop w (Suc l))) (Suc j))"
  def w3  == "fst (bv_chop (snd (bv_chop (snd (bv_chop w (Suc l))) (Suc j))) i)"
  def w4  == "fst (bv_chop (snd (bv_chop (snd (bv_chop (snd (bv_chop w (Suc l))) (Suc j))) i)) k)"
  def w5  == "snd (bv_chop (snd (bv_chop (snd (bv_chop (snd (bv_chop w (Suc l))) (Suc j))) i)) k)"

  note w_defs = w1_def w2_def w3_def w4_def w5_def

  have w_def: "w = w1 @ w2 @ w3 @ w4 @ w5"
    by (simp add: w_defs append_bv_chop_id)

  from ki ij jl lw
  show ?thesis
    apply (subst bv_sliceI [where ?j = i and ?i = j and ?w = w and ?w1.0 = "w1 @ w2" and ?w2.0 = w3 and ?w3.0 = "w4 @ w5"])
    apply simp_all
    apply (rule w_def)
    apply (simp add: w_defs min_def)
    apply (simp add: w_defs min_def)
    apply (subst bv_sliceI [where ?j = k and ?i = l and ?w = w and ?w1.0 = w1 and ?w2.0 = "w2 @ w3 @ w4" and ?w3.0 = w5])
    apply simp_all
    apply (rule w_def)
    apply (simp add: w_defs min_def)
    apply (simp add: w_defs min_def)
    apply (subst bv_sliceI [where ?j = "i-k" and ?i = "j-k" and ?w = "w2 @ w3 @ w4" and ?w1.0 = w2 and ?w2.0 = w3 and ?w3.0 = w4])
    apply simp_all
    apply (simp_all add: w_defs min_def)
    apply arith+
    done
qed

lemma bv_to_nat_extend [simp]: "bv_to_nat (bv_extend n \<zero> w) = bv_to_nat w"
  apply (simp add: bv_extend_def)
  apply (subst bv_to_nat_dist_append)
  apply simp
  apply (induct "n - length w",simp_all)
  done

lemma bv_msb_extend_same [simp]: "bv_msb w = b ==> bv_msb (bv_extend n b w) = b"
  apply (simp add: bv_extend_def)
  apply (induct "n - length w",simp_all)
  done

lemma bv_to_int_extend [simp]:
  assumes a: "bv_msb w = b"
  shows      "bv_to_int (bv_extend n b w) = bv_to_int w"
proof (cases "bv_msb w")
  assume [simp]: "bv_msb w = \<zero>"
  with a have [simp]: "b = \<zero>"
    by simp
  show ?thesis
    by (simp add: bv_to_int_def)
next
  assume [simp]: "bv_msb w = \<one>"
  with a have [simp]: "b = \<one>"
    by simp
  show ?thesis
    apply (simp add: bv_to_int_def)
    apply (simp add: bv_extend_def)
    apply (induct "n - length w",simp_all)
    done
qed

lemma length_nat_mono [simp]: "x \<le> y ==> length_nat x \<le> length_nat y"
proof (rule ccontr)
  assume xy: "x \<le> y"
  assume "~ length_nat x \<le> length_nat y"
  hence lxly: "length_nat y < length_nat x"
    by simp
  hence "length_nat y < (LEAST n. x < 2 ^ n)"
    by (simp add: length_nat_def)
  hence "~ x < 2 ^ length_nat y"
    by (rule not_less_Least)
  hence xx: "2 ^ length_nat y \<le> x"
    by simp
  have yy: "y < 2 ^ length_nat y"
    apply (simp add: length_nat_def)
    apply (rule LeastI)
    apply (subgoal_tac "y < 2 ^ (nat y)",assumption)
    apply (cases "0 \<le> y")
    apply (subgoal_tac "int (nat y) < int (2 ^ nat y)")
    apply (simp add: int_nat_two_exp)
    apply (induct "nat y",simp_all)
    done
  with xx
  have "y < x" by simp
  with xy
  show False
    by simp
qed

lemma length_nat_mono_int [simp]: "x \<le> y ==> length_nat x \<le> length_nat y"
  apply (rule length_nat_mono)
  apply arith
  done

lemma length_nat_pos [simp,intro!]: "0 < x ==> 0 < length_nat x"
  by (simp add: length_nat_non0)

lemma length_int_mono_gt0: "[| 0 \<le> x ; x \<le> y |] ==> length_int x \<le> length_int y"
  by (cases "x = 0",simp_all add: length_int_gt0)

lemma length_int_mono_lt0: "[| x \<le> y ; y \<le> 0 |] ==> length_int y \<le> length_int x"
  by (cases "y = 0",simp_all add: length_int_lt0)

lemmas [simp] = length_nat_non0

lemma "nat_to_bv (number_of bin.Pls) = []"
  by simp

consts
  fast_nat_to_bv_helper :: "bin => bit list => bit list"

primrec
  fast_nat_to_bv_Pls: "fast_nat_to_bv_helper bin.Pls res = res"
  fast_nat_to_bv_Bit: "fast_nat_to_bv_helper (w BIT b) res = fast_nat_to_bv_helper w ((if b then \<one> else \<zero>) # res)"

lemma fast_nat_to_bv_def:
  assumes pos_w: "(0::int) \<le> number_of w"
  shows "nat_to_bv (number_of w) == norm_unsigned (fast_nat_to_bv_helper w [])"
proof -
  have h [rule_format]: "(0::int) \<le> number_of w ==> \<forall> l. norm_unsigned (nat_to_bv_helper (number_of w) l) = norm_unsigned (fast_nat_to_bv_helper w l)"
  proof (induct w,simp add: nat_to_bv_helper.simps,simp)
    fix bin b
    assume ind: "(0::int) \<le> number_of bin ==> \<forall> l. norm_unsigned (nat_to_bv_helper (number_of bin) l) = norm_unsigned (fast_nat_to_bv_helper bin l)"
    def qq == "number_of bin::int"
    assume posbb: "(0::int) \<le> number_of (bin BIT b)"
    hence indq [rule_format]: "\<forall> l. norm_unsigned (nat_to_bv_helper qq l) = norm_unsigned (fast_nat_to_bv_helper bin l)"
      apply (unfold qq_def)
      apply (rule ind)
      apply simp
      done
    from posbb
    have "0 \<le> qq"
      by (simp add: qq_def)
    with posbb
    show "\<forall> l. norm_unsigned (nat_to_bv_helper (number_of (bin BIT b)) l) = norm_unsigned (fast_nat_to_bv_helper (bin BIT b) l)"
      apply (subst pos_number_of,simp)
      apply safe
      apply (fold qq_def)
      apply (cases "qq = 0")
      apply (simp add: nat_to_bv_helper.simps)
      apply (subst indq [symmetric])
      apply (subst indq [symmetric])
      apply (simp add: nat_to_bv_helper.simps)
      apply (subgoal_tac "0 < qq")
      prefer 2
      apply simp
      apply simp
      apply (subst indq [symmetric])
      apply (subst indq [symmetric])
      apply auto
      apply (subst nat_to_bv_helper.simps [of "2 * qq + 1"])
      apply simp
      apply safe
      apply (subgoal_tac "2 * qq + 1 ~= 2 * q")
      apply simp
      apply arith
      apply (subgoal_tac "(2 * qq + 1) div 2 = qq")
      apply simp
      apply (subst zdiv_zadd1_eq,simp)
      apply (subst nat_to_bv_helper.simps [of "2 * qq"])
      apply simp
      done
  qed
  from pos_w
  have "nat_to_bv (number_of w) = norm_unsigned (nat_to_bv (number_of w))"
    by simp
  also have "... = norm_unsigned (fast_nat_to_bv_helper w [])"
    apply (unfold nat_to_bv_def)
    apply (rule h)
    apply (rule pos_w)
    done
  finally show "nat_to_bv (number_of w) == norm_unsigned (fast_nat_to_bv_helper w [])"
    by simp
qed

lemma fast_nat_to_bv_Bit0: "fast_nat_to_bv_helper (w BIT False) res = fast_nat_to_bv_helper w (\<zero> # res)"
  by simp

lemma fast_nat_to_bv_Bit1: "fast_nat_to_bv_helper (w BIT True) res = fast_nat_to_bv_helper w (\<one> # res)"
  by simp

declare fast_nat_to_bv_Bit [simp del]
declare fast_nat_to_bv_Bit0 [simp]
declare fast_nat_to_bv_Bit1 [simp]

consts
  fast_bv_to_nat_helper :: "[bit list, bin] => bin"

primrec
  fast_bv_to_nat_Nil: "fast_bv_to_nat_helper [] bin = bin"
  fast_bv_to_nat_Cons: "fast_bv_to_nat_helper (b#bs) bin = fast_bv_to_nat_helper bs (bin BIT (bit_case False True b))"

lemma fast_bv_to_nat_Cons0: "fast_bv_to_nat_helper (\<zero>#bs) bin = fast_bv_to_nat_helper bs (bin BIT False)"
  by simp

lemma fast_bv_to_nat_Cons1: "fast_bv_to_nat_helper (\<one>#bs) bin = fast_bv_to_nat_helper bs (bin BIT True)"
  by simp

lemma fast_bv_to_nat_def: "bv_to_nat bs == number_of (fast_bv_to_nat_helper bs bin.Pls)"
proof (simp add: bv_to_nat_def)
  have "\<forall> bin. (foldl (%bn b. bn BIT (b = \<one>)) bin bs) = (fast_bv_to_nat_helper bs bin)"
    apply (induct bs,simp)
    apply (case_tac a,simp_all)
    done
  thus "number_of (foldl (%bn b. bn BIT (b = \<one>)) bin.Pls bs) == number_of (fast_bv_to_nat_helper bs bin.Pls)::int"
    by simp
qed

declare fast_bv_to_nat_Cons [simp del]
declare fast_bv_to_nat_Cons0 [simp]
declare fast_bv_to_nat_Cons1 [simp]

setup setup_word

declare bv_to_nat1 [simp del]
declare bv_to_nat_helper [simp del]

constdefs
  bv_mapzip :: "[bit => bit => bit,bit list, bit list] => bit list"
  "bv_mapzip f w1 w2 == let g = bv_extend (max (length w1) (length w2)) \<zero>
                        in map (split f) (zip (g w1) (g w2))"

lemma bv_length_bv_mapzip [simp]: "length (bv_mapzip f w1 w2) = max (length w1) (length w2)"
  by (simp add: bv_mapzip_def Let_def split: split_max)

lemma [simp]: "bv_mapzip f [] [] = []"
  by (simp add: bv_mapzip_def Let_def)

lemma [simp]: "length w1 = length w2 ==> bv_mapzip f (x#w1) (y#w2) = f x y # bv_mapzip f w1 w2"
  by (simp add: bv_mapzip_def Let_def)

lemma [code]: "bv_to_nat bs = list_rec (0::int) (\<lambda>b bs n. bitval b * 2 ^ length bs + n) bs"
  by (induct bs,simp_all add: bv_to_nat_helper)

text {* The following can be added for speedup, but depends on the
exact definition of division and modulo of the ML compiler for soundness. *}

(*
consts_code "op div" ("'('(_') div '(_')')")
consts_code "op mod" ("'('(_') mod '(_')')")
*)

end
