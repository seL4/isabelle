(*  Title:      HOL/Code_Numeral.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Numeric types for code generation onto target language numerals only\<close>

theory Code_Numeral
imports Divides Lifting Bit_Operations
begin

subsection \<open>Type of target language integers\<close>

typedef integer = "UNIV :: int set"
  morphisms int_of_integer integer_of_int ..

setup_lifting type_definition_integer

lemma integer_eq_iff:
  "k = l \<longleftrightarrow> int_of_integer k = int_of_integer l"
  by transfer rule

lemma integer_eqI:
  "int_of_integer k = int_of_integer l \<Longrightarrow> k = l"
  using integer_eq_iff [of k l] by simp

lemma int_of_integer_integer_of_int [simp]:
  "int_of_integer (integer_of_int k) = k"
  by transfer rule

lemma integer_of_int_int_of_integer [simp]:
  "integer_of_int (int_of_integer k) = k"
  by transfer rule

instantiation integer :: ring_1
begin

lift_definition zero_integer :: integer
  is "0 :: int"
  .

declare zero_integer.rep_eq [simp]

lift_definition one_integer :: integer
  is "1 :: int"
  .

declare one_integer.rep_eq [simp]

lift_definition plus_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer"
  is "plus :: int \<Rightarrow> int \<Rightarrow> int"
  .

declare plus_integer.rep_eq [simp]

lift_definition uminus_integer :: "integer \<Rightarrow> integer"
  is "uminus :: int \<Rightarrow> int"
  .

declare uminus_integer.rep_eq [simp]

lift_definition minus_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer"
  is "minus :: int \<Rightarrow> int \<Rightarrow> int"
  .

declare minus_integer.rep_eq [simp]

lift_definition times_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer"
  is "times :: int \<Rightarrow> int \<Rightarrow> int"
  .

declare times_integer.rep_eq [simp]

instance proof
qed (transfer, simp add: algebra_simps)+

end

instance integer :: Rings.dvd ..

context
  includes lifting_syntax
  notes transfer_rule_numeral [transfer_rule]
begin

lemma [transfer_rule]:
  "(pcr_integer ===> pcr_integer ===> (\<longleftrightarrow>)) (dvd) (dvd)"
  by (unfold dvd_def) transfer_prover

lemma [transfer_rule]:
  "((\<longleftrightarrow>) ===> pcr_integer) of_bool of_bool"
  by (unfold of_bool_def) transfer_prover

lemma [transfer_rule]:
  "((=) ===> pcr_integer) int of_nat"
  by (rule transfer_rule_of_nat) transfer_prover+

lemma [transfer_rule]:
  "((=) ===> pcr_integer) (\<lambda>k. k) of_int"
proof -
  have "((=) ===> pcr_integer) of_int of_int"
    by (rule transfer_rule_of_int) transfer_prover+
  then show ?thesis by (simp add: id_def)
qed

lemma [transfer_rule]:
  "((=) ===> pcr_integer) numeral numeral"
  by transfer_prover

lemma [transfer_rule]:
  "((=) ===> (=) ===> pcr_integer) Num.sub Num.sub"
  by (unfold Num.sub_def) transfer_prover

lemma [transfer_rule]:
  "(pcr_integer ===> (=) ===> pcr_integer) (^) (^)"
  by (unfold power_def) transfer_prover

end

lemma int_of_integer_of_nat [simp]:
  "int_of_integer (of_nat n) = of_nat n"
  by transfer rule

lift_definition integer_of_nat :: "nat \<Rightarrow> integer"
  is "of_nat :: nat \<Rightarrow> int"
  .

lemma integer_of_nat_eq_of_nat [code]:
  "integer_of_nat = of_nat"
  by transfer rule

lemma int_of_integer_integer_of_nat [simp]:
  "int_of_integer (integer_of_nat n) = of_nat n"
  by transfer rule

lift_definition nat_of_integer :: "integer \<Rightarrow> nat"
  is Int.nat
  .

lemma nat_of_integer_of_nat [simp]:
  "nat_of_integer (of_nat n) = n"
  by transfer simp

lemma int_of_integer_of_int [simp]:
  "int_of_integer (of_int k) = k"
  by transfer simp

lemma nat_of_integer_integer_of_nat [simp]:
  "nat_of_integer (integer_of_nat n) = n"
  by transfer simp

lemma integer_of_int_eq_of_int [simp, code_abbrev]:
  "integer_of_int = of_int"
  by transfer (simp add: fun_eq_iff)

lemma of_int_integer_of [simp]:
  "of_int (int_of_integer k) = (k :: integer)"
  by transfer rule

lemma int_of_integer_numeral [simp]:
  "int_of_integer (numeral k) = numeral k"
  by transfer rule

lemma int_of_integer_sub [simp]:
  "int_of_integer (Num.sub k l) = Num.sub k l"
  by transfer rule

definition integer_of_num :: "num \<Rightarrow> integer"
  where [simp]: "integer_of_num = numeral"

lemma integer_of_num [code]:
  "integer_of_num Num.One = 1"
  "integer_of_num (Num.Bit0 n) = (let k = integer_of_num n in k + k)"
  "integer_of_num (Num.Bit1 n) = (let k = integer_of_num n in k + k + 1)"
  by (simp_all only: integer_of_num_def numeral.simps Let_def)

lemma integer_of_num_triv:
  "integer_of_num Num.One = 1"
  "integer_of_num (Num.Bit0 Num.One) = 2"
  by simp_all

instantiation integer :: "{linordered_idom, equal}"
begin

lift_definition abs_integer :: "integer \<Rightarrow> integer"
  is "abs :: int \<Rightarrow> int"
  .

declare abs_integer.rep_eq [simp]

lift_definition sgn_integer :: "integer \<Rightarrow> integer"
  is "sgn :: int \<Rightarrow> int"
  .

declare sgn_integer.rep_eq [simp]

lift_definition less_eq_integer :: "integer \<Rightarrow> integer \<Rightarrow> bool"
  is "less_eq :: int \<Rightarrow> int \<Rightarrow> bool"
  .

lemma integer_less_eq_iff:
  "k \<le> l \<longleftrightarrow> int_of_integer k \<le> int_of_integer l"
  by (fact less_eq_integer.rep_eq)

lift_definition less_integer :: "integer \<Rightarrow> integer \<Rightarrow> bool"
  is "less :: int \<Rightarrow> int \<Rightarrow> bool"
  .

lemma integer_less_iff:
  "k < l \<longleftrightarrow> int_of_integer k < int_of_integer l"
  by (fact less_integer.rep_eq)

lift_definition equal_integer :: "integer \<Rightarrow> integer \<Rightarrow> bool"
  is "HOL.equal :: int \<Rightarrow> int \<Rightarrow> bool"
  .

instance
  by standard (transfer, simp add: algebra_simps equal less_le_not_le [symmetric] mult_strict_right_mono linear)+

end

context
  includes lifting_syntax
begin

lemma [transfer_rule]:
  \<open>(pcr_integer ===> pcr_integer ===> pcr_integer) min min\<close>
  by (unfold min_def) transfer_prover

lemma [transfer_rule]:
  \<open>(pcr_integer ===> pcr_integer ===> pcr_integer) max max\<close>
  by (unfold max_def) transfer_prover

end

lemma int_of_integer_min [simp]:
  "int_of_integer (min k l) = min (int_of_integer k) (int_of_integer l)"
  by transfer rule

lemma int_of_integer_max [simp]:
  "int_of_integer (max k l) = max (int_of_integer k) (int_of_integer l)"
  by transfer rule

lemma nat_of_integer_non_positive [simp]:
  "k \<le> 0 \<Longrightarrow> nat_of_integer k = 0"
  by transfer simp

lemma of_nat_of_integer [simp]:
  "of_nat (nat_of_integer k) = max 0 k"
  by transfer auto

instantiation integer :: unique_euclidean_ring
begin

lift_definition divide_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer"
  is "divide :: int \<Rightarrow> int \<Rightarrow> int"
  .

declare divide_integer.rep_eq [simp]

lift_definition modulo_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer"
  is "modulo :: int \<Rightarrow> int \<Rightarrow> int"
  .

declare modulo_integer.rep_eq [simp]

lift_definition euclidean_size_integer :: "integer \<Rightarrow> nat"
  is "euclidean_size :: int \<Rightarrow> nat"
  .

declare euclidean_size_integer.rep_eq [simp]

lift_definition division_segment_integer :: "integer \<Rightarrow> integer"
  is "division_segment :: int \<Rightarrow> int"
  .

declare division_segment_integer.rep_eq [simp]

instance
  by (standard; transfer)
    (use mult_le_mono2 [of 1] in \<open>auto simp add: sgn_mult_abs abs_mult sgn_mult abs_mod_less sgn_mod nat_mult_distrib
     division_segment_mult division_segment_mod intro: div_eqI\<close>)

end

lemma [code]:
  "euclidean_size = nat_of_integer \<circ> abs"
  by (simp add: fun_eq_iff nat_of_integer.rep_eq)

lemma [code]:
  "division_segment (k :: integer) = (if k \<ge> 0 then 1 else - 1)"
  by transfer (simp add: division_segment_int_def)

instance integer :: unique_euclidean_ring_with_nat
  by (standard; transfer) (simp_all add: of_nat_div division_segment_int_def)

instantiation integer :: semiring_bit_shifts
begin

lift_definition bit_integer :: \<open>integer \<Rightarrow> nat \<Rightarrow> bool\<close>
  is bit .

lift_definition push_bit_integer :: \<open>nat \<Rightarrow> integer \<Rightarrow> integer\<close>
  is push_bit .

lift_definition drop_bit_integer :: \<open>nat \<Rightarrow> integer \<Rightarrow> integer\<close>
  is drop_bit .

lift_definition take_bit_integer :: \<open>nat \<Rightarrow> integer \<Rightarrow> integer\<close>
  is take_bit .

instance by (standard; transfer)
  (fact bit_eq_rec bits_induct bit_iff_odd push_bit_eq_mult drop_bit_eq_div take_bit_eq_mod
    bits_div_0 bits_div_by_1 bits_mod_div_trivial even_succ_div_2
    exp_div_exp_eq div_exp_eq mod_exp_eq mult_exp_mod_exp_eq div_exp_mod_exp_eq
    even_mask_div_iff even_mult_exp_div_exp_iff)+

end

instance integer :: unique_euclidean_semiring_with_bit_shifts ..

lemma [code]:
  \<open>bit k n \<longleftrightarrow> odd (drop_bit n k)\<close>
  \<open>push_bit n k = k * 2 ^ n\<close>
  \<open>drop_bit n k = k div 2 ^ n\<close>
  \<open>take_bit n k = k mod 2 ^ n\<close> for k :: integer
  by (fact bit_iff_odd_drop_bit push_bit_eq_mult drop_bit_eq_div take_bit_eq_mod)+

instantiation integer :: unique_euclidean_semiring_numeral
begin

definition divmod_integer :: "num \<Rightarrow> num \<Rightarrow> integer \<times> integer"
where
  divmod_integer'_def: "divmod_integer m n = (numeral m div numeral n, numeral m mod numeral n)"

definition divmod_step_integer :: "num \<Rightarrow> integer \<times> integer \<Rightarrow> integer \<times> integer"
where
  "divmod_step_integer l qr = (let (q, r) = qr
    in if r \<ge> numeral l then (2 * q + 1, r - numeral l)
    else (2 * q, r))"

instance proof
  show "divmod m n = (numeral m div numeral n :: integer, numeral m mod numeral n)"
    for m n by (fact divmod_integer'_def)
  show "divmod_step l qr = (let (q, r) = qr
    in if r \<ge> numeral l then (2 * q + 1, r - numeral l)
    else (2 * q, r))" for l and qr :: "integer \<times> integer"
    by (fact divmod_step_integer_def)
qed (transfer,
  fact le_add_diff_inverse2
  unique_euclidean_semiring_numeral_class.div_less
  unique_euclidean_semiring_numeral_class.mod_less
  unique_euclidean_semiring_numeral_class.div_positive
  unique_euclidean_semiring_numeral_class.mod_less_eq_dividend
  unique_euclidean_semiring_numeral_class.pos_mod_bound
  unique_euclidean_semiring_numeral_class.pos_mod_sign
  unique_euclidean_semiring_numeral_class.mod_mult2_eq
  unique_euclidean_semiring_numeral_class.div_mult2_eq
  unique_euclidean_semiring_numeral_class.discrete)+

end

declare divmod_algorithm_code [where ?'a = integer,
  folded integer_of_num_def, unfolded integer_of_num_triv,
  code]

lemma integer_of_nat_0: "integer_of_nat 0 = 0"
by transfer simp

lemma integer_of_nat_1: "integer_of_nat 1 = 1"
by transfer simp

lemma integer_of_nat_numeral:
  "integer_of_nat (numeral n) = numeral n"
by transfer simp


subsection \<open>Code theorems for target language integers\<close>

text \<open>Constructors\<close>

definition Pos :: "num \<Rightarrow> integer"
where
  [simp, code_post]: "Pos = numeral"

context
  includes lifting_syntax
begin

lemma [transfer_rule]:
  \<open>((=) ===> pcr_integer) numeral Pos\<close>
  by simp transfer_prover

end

lemma Pos_fold [code_unfold]:
  "numeral Num.One = Pos Num.One"
  "numeral (Num.Bit0 k) = Pos (Num.Bit0 k)"
  "numeral (Num.Bit1 k) = Pos (Num.Bit1 k)"
  by simp_all

definition Neg :: "num \<Rightarrow> integer"
where
  [simp, code_abbrev]: "Neg n = - Pos n"

context
  includes lifting_syntax
begin

lemma [transfer_rule]:
  \<open>((=) ===> pcr_integer) (\<lambda>n. - numeral n) Neg\<close>
  by (unfold Neg_def) transfer_prover

end

code_datatype "0::integer" Pos Neg

  
text \<open>A further pair of constructors for generated computations\<close>

context
begin  

qualified definition positive :: "num \<Rightarrow> integer"
  where [simp]: "positive = numeral"

qualified definition negative :: "num \<Rightarrow> integer"
  where [simp]: "negative = uminus \<circ> numeral"

lemma [code_computation_unfold]:
  "numeral = positive"
  "Pos = positive"
  "Neg = negative"
  by (simp_all add: fun_eq_iff)

end


text \<open>Auxiliary operations\<close>

lift_definition dup :: "integer \<Rightarrow> integer"
  is "\<lambda>k::int. k + k"
  .

lemma dup_code [code]:
  "dup 0 = 0"
  "dup (Pos n) = Pos (Num.Bit0 n)"
  "dup (Neg n) = Neg (Num.Bit0 n)"
  by (transfer, simp only: numeral_Bit0 minus_add_distrib)+

lift_definition sub :: "num \<Rightarrow> num \<Rightarrow> integer"
  is "\<lambda>m n. numeral m - numeral n :: int"
  .

lemma sub_code [code]:
  "sub Num.One Num.One = 0"
  "sub (Num.Bit0 m) Num.One = Pos (Num.BitM m)"
  "sub (Num.Bit1 m) Num.One = Pos (Num.Bit0 m)"
  "sub Num.One (Num.Bit0 n) = Neg (Num.BitM n)"
  "sub Num.One (Num.Bit1 n) = Neg (Num.Bit0 n)"
  "sub (Num.Bit0 m) (Num.Bit0 n) = dup (sub m n)"
  "sub (Num.Bit1 m) (Num.Bit1 n) = dup (sub m n)"
  "sub (Num.Bit1 m) (Num.Bit0 n) = dup (sub m n) + 1"
  "sub (Num.Bit0 m) (Num.Bit1 n) = dup (sub m n) - 1"
  by (transfer, simp add: dbl_def dbl_inc_def dbl_dec_def)+


text \<open>Implementations\<close>

lemma one_integer_code [code, code_unfold]:
  "1 = Pos Num.One"
  by simp

lemma plus_integer_code [code]:
  "k + 0 = (k::integer)"
  "0 + l = (l::integer)"
  "Pos m + Pos n = Pos (m + n)"
  "Pos m + Neg n = sub m n"
  "Neg m + Pos n = sub n m"
  "Neg m + Neg n = Neg (m + n)"
  by (transfer, simp)+

lemma uminus_integer_code [code]:
  "uminus 0 = (0::integer)"
  "uminus (Pos m) = Neg m"
  "uminus (Neg m) = Pos m"
  by simp_all

lemma minus_integer_code [code]:
  "k - 0 = (k::integer)"
  "0 - l = uminus (l::integer)"
  "Pos m - Pos n = sub m n"
  "Pos m - Neg n = Pos (m + n)"
  "Neg m - Pos n = Neg (m + n)"
  "Neg m - Neg n = sub n m"
  by (transfer, simp)+

lemma abs_integer_code [code]:
  "\<bar>k\<bar> = (if (k::integer) < 0 then - k else k)"
  by simp

lemma sgn_integer_code [code]:
  "sgn k = (if k = 0 then 0 else if (k::integer) < 0 then - 1 else 1)"
  by simp

lemma times_integer_code [code]:
  "k * 0 = (0::integer)"
  "0 * l = (0::integer)"
  "Pos m * Pos n = Pos (m * n)"
  "Pos m * Neg n = Neg (m * n)"
  "Neg m * Pos n = Neg (m * n)"
  "Neg m * Neg n = Pos (m * n)"
  by simp_all

definition divmod_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer \<times> integer"
where
  "divmod_integer k l = (k div l, k mod l)"

lemma fst_divmod_integer [simp]:
  "fst (divmod_integer k l) = k div l"
  by (simp add: divmod_integer_def)

lemma snd_divmod_integer [simp]:
  "snd (divmod_integer k l) = k mod l"
  by (simp add: divmod_integer_def)

definition divmod_abs :: "integer \<Rightarrow> integer \<Rightarrow> integer \<times> integer"
where
  "divmod_abs k l = (\<bar>k\<bar> div \<bar>l\<bar>, \<bar>k\<bar> mod \<bar>l\<bar>)"

lemma fst_divmod_abs [simp]:
  "fst (divmod_abs k l) = \<bar>k\<bar> div \<bar>l\<bar>"
  by (simp add: divmod_abs_def)

lemma snd_divmod_abs [simp]:
  "snd (divmod_abs k l) = \<bar>k\<bar> mod \<bar>l\<bar>"
  by (simp add: divmod_abs_def)

lemma divmod_abs_code [code]:
  "divmod_abs (Pos k) (Pos l) = divmod k l"
  "divmod_abs (Neg k) (Neg l) = divmod k l"
  "divmod_abs (Neg k) (Pos l) = divmod k l"
  "divmod_abs (Pos k) (Neg l) = divmod k l"
  "divmod_abs j 0 = (0, \<bar>j\<bar>)"
  "divmod_abs 0 j = (0, 0)"
  by (simp_all add: prod_eq_iff)

lemma divmod_integer_eq_cases:
  "divmod_integer k l =
    (if k = 0 then (0, 0) else if l = 0 then (0, k) else
    (apsnd \<circ> times \<circ> sgn) l (if sgn k = sgn l
      then divmod_abs k l
      else (let (r, s) = divmod_abs k l in
        if s = 0 then (- r, 0) else (- r - 1, \<bar>l\<bar> - s))))"
proof -
  have *: "sgn k = sgn l \<longleftrightarrow> k = 0 \<and> l = 0 \<or> 0 < l \<and> 0 < k \<or> l < 0 \<and> k < 0" for k l :: int
    by (auto simp add: sgn_if)
  have **: "- k = l * q \<longleftrightarrow> k = - (l * q)" for k l q :: int
    by auto
  show ?thesis
    by (simp add: divmod_integer_def divmod_abs_def)
      (transfer, auto simp add: * ** not_less zdiv_zminus1_eq_if zmod_zminus1_eq_if div_minus_right mod_minus_right)
qed

lemma divmod_integer_code [code]: \<^marker>\<open>contributor \<open>René Thiemann\<close>\<close> \<^marker>\<open>contributor \<open>Akihisa Yamada\<close>\<close>
  "divmod_integer k l =
   (if k = 0 then (0, 0)
    else if l > 0 then
            (if k > 0 then Code_Numeral.divmod_abs k l
             else case Code_Numeral.divmod_abs k l of (r, s) \<Rightarrow>
                  if s = 0 then (- r, 0) else (- r - 1, l - s))
    else if l = 0 then (0, k)
    else apsnd uminus
            (if k < 0 then Code_Numeral.divmod_abs k l
             else case Code_Numeral.divmod_abs k l of (r, s) \<Rightarrow>
                  if s = 0 then (- r, 0) else (- r - 1, - l - s)))"
  by (cases l "0 :: integer" rule: linorder_cases)
    (auto split: prod.splits simp add: divmod_integer_eq_cases)

lemma div_integer_code [code]:
  "k div l = fst (divmod_integer k l)"
  by simp

lemma mod_integer_code [code]:
  "k mod l = snd (divmod_integer k l)"
  by simp

definition bit_cut_integer :: "integer \<Rightarrow> integer \<times> bool"
  where "bit_cut_integer k = (k div 2, odd k)"

lemma bit_cut_integer_code [code]:
  "bit_cut_integer k = (if k = 0 then (0, False)
     else let (r, s) = Code_Numeral.divmod_abs k 2
       in (if k > 0 then r else - r - s, s = 1))"
proof -
  have "bit_cut_integer k = (let (r, s) = divmod_integer k 2 in (r, s = 1))"
    by (simp add: divmod_integer_def bit_cut_integer_def odd_iff_mod_2_eq_one)
  then show ?thesis
    by (simp add: divmod_integer_code) (auto simp add: split_def)
qed

lemma equal_integer_code [code]:
  "HOL.equal 0 (0::integer) \<longleftrightarrow> True"
  "HOL.equal 0 (Pos l) \<longleftrightarrow> False"
  "HOL.equal 0 (Neg l) \<longleftrightarrow> False"
  "HOL.equal (Pos k) 0 \<longleftrightarrow> False"
  "HOL.equal (Pos k) (Pos l) \<longleftrightarrow> HOL.equal k l"
  "HOL.equal (Pos k) (Neg l) \<longleftrightarrow> False"
  "HOL.equal (Neg k) 0 \<longleftrightarrow> False"
  "HOL.equal (Neg k) (Pos l) \<longleftrightarrow> False"
  "HOL.equal (Neg k) (Neg l) \<longleftrightarrow> HOL.equal k l"
  by (simp_all add: equal)

lemma equal_integer_refl [code nbe]:
  "HOL.equal (k::integer) k \<longleftrightarrow> True"
  by (fact equal_refl)

lemma less_eq_integer_code [code]:
  "0 \<le> (0::integer) \<longleftrightarrow> True"
  "0 \<le> Pos l \<longleftrightarrow> True"
  "0 \<le> Neg l \<longleftrightarrow> False"
  "Pos k \<le> 0 \<longleftrightarrow> False"
  "Pos k \<le> Pos l \<longleftrightarrow> k \<le> l"
  "Pos k \<le> Neg l \<longleftrightarrow> False"
  "Neg k \<le> 0 \<longleftrightarrow> True"
  "Neg k \<le> Pos l \<longleftrightarrow> True"
  "Neg k \<le> Neg l \<longleftrightarrow> l \<le> k"
  by simp_all

lemma less_integer_code [code]:
  "0 < (0::integer) \<longleftrightarrow> False"
  "0 < Pos l \<longleftrightarrow> True"
  "0 < Neg l \<longleftrightarrow> False"
  "Pos k < 0 \<longleftrightarrow> False"
  "Pos k < Pos l \<longleftrightarrow> k < l"
  "Pos k < Neg l \<longleftrightarrow> False"
  "Neg k < 0 \<longleftrightarrow> True"
  "Neg k < Pos l \<longleftrightarrow> True"
  "Neg k < Neg l \<longleftrightarrow> l < k"
  by simp_all

lift_definition num_of_integer :: "integer \<Rightarrow> num"
  is "num_of_nat \<circ> nat"
  .

lemma num_of_integer_code [code]:
  "num_of_integer k = (if k \<le> 1 then Num.One
     else let
       (l, j) = divmod_integer k 2;
       l' = num_of_integer l;
       l'' = l' + l'
     in if j = 0 then l'' else l'' + Num.One)"
proof -
  {
    assume "int_of_integer k mod 2 = 1"
    then have "nat (int_of_integer k mod 2) = nat 1" by simp
    moreover assume *: "1 < int_of_integer k"
    ultimately have **: "nat (int_of_integer k) mod 2 = 1" by (simp add: nat_mod_distrib)
    have "num_of_nat (nat (int_of_integer k)) =
      num_of_nat (2 * (nat (int_of_integer k) div 2) + nat (int_of_integer k) mod 2)"
      by simp
    then have "num_of_nat (nat (int_of_integer k)) =
      num_of_nat (nat (int_of_integer k) div 2 + nat (int_of_integer k) div 2 + nat (int_of_integer k) mod 2)"
      by (simp add: mult_2)
    with ** have "num_of_nat (nat (int_of_integer k)) =
      num_of_nat (nat (int_of_integer k) div 2 + nat (int_of_integer k) div 2 + 1)"
      by simp
  }
  note aux = this
  show ?thesis
    by (auto simp add: num_of_integer_def nat_of_integer_def Let_def case_prod_beta
      not_le integer_eq_iff less_eq_integer_def
      nat_mult_distrib nat_div_distrib num_of_nat_One num_of_nat_plus_distrib
       mult_2 [where 'a=nat] aux add_One)
qed

lemma nat_of_integer_code [code]:
  "nat_of_integer k = (if k \<le> 0 then 0
     else let
       (l, j) = divmod_integer k 2;
       l' = nat_of_integer l;
       l'' = l' + l'
     in if j = 0 then l'' else l'' + 1)"
proof -
  obtain j where k: "k = integer_of_int j"
  proof
    show "k = integer_of_int (int_of_integer k)" by simp
  qed
  have *: "nat j mod 2 = nat_of_integer (of_int j mod 2)" if "j \<ge> 0"
    using that by transfer (simp add: nat_mod_distrib)
  from k show ?thesis
    by (auto simp add: split_def Let_def nat_of_integer_def nat_div_distrib mult_2 [symmetric]
      minus_mod_eq_mult_div [symmetric] *)
qed

lemma int_of_integer_code [code]:
  "int_of_integer k = (if k < 0 then - (int_of_integer (- k))
     else if k = 0 then 0
     else let
       (l, j) = divmod_integer k 2;
       l' = 2 * int_of_integer l
     in if j = 0 then l' else l' + 1)"
  by (auto simp add: split_def Let_def integer_eq_iff minus_mod_eq_mult_div [symmetric])

lemma integer_of_int_code [code]:
  "integer_of_int k = (if k < 0 then - (integer_of_int (- k))
     else if k = 0 then 0
     else let
       l = 2 * integer_of_int (k div 2);
       j = k mod 2
     in if j = 0 then l else l + 1)"
  by (auto simp add: split_def Let_def integer_eq_iff minus_mod_eq_mult_div [symmetric])

hide_const (open) Pos Neg sub dup divmod_abs


subsection \<open>Serializer setup for target language integers\<close>

code_reserved Eval int Integer abs

code_printing
  type_constructor integer \<rightharpoonup>
    (SML) "IntInf.int"
    and (OCaml) "Z.t"
    and (Haskell) "Integer"
    and (Scala) "BigInt"
    and (Eval) "int"
| class_instance integer :: equal \<rightharpoonup>
    (Haskell) -

code_printing
  constant "0::integer" \<rightharpoonup>
    (SML) "!(0/ :/ IntInf.int)"
    and (OCaml) "Z.zero"
    and (Haskell) "!(0/ ::/ Integer)"
    and (Scala) "BigInt(0)"

setup \<open>
  fold (fn target =>
    Numeral.add_code \<^const_name>\<open>Code_Numeral.Pos\<close> I Code_Printer.literal_numeral target
    #> Numeral.add_code \<^const_name>\<open>Code_Numeral.Neg\<close> (~) Code_Printer.literal_numeral target)
    ["SML", "OCaml", "Haskell", "Scala"]
\<close>

code_printing
  constant "plus :: integer \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (SML) "IntInf.+ ((_), (_))"
    and (OCaml) "Z.add"
    and (Haskell) infixl 6 "+"
    and (Scala) infixl 7 "+"
    and (Eval) infixl 8 "+"
| constant "uminus :: integer \<Rightarrow> _" \<rightharpoonup>
    (SML) "IntInf.~"
    and (OCaml) "Z.neg"
    and (Haskell) "negate"
    and (Scala) "!(- _)"
    and (Eval) "~/ _"
| constant "minus :: integer \<Rightarrow> _" \<rightharpoonup>
    (SML) "IntInf.- ((_), (_))"
    and (OCaml) "Z.sub"
    and (Haskell) infixl 6 "-"
    and (Scala) infixl 7 "-"
    and (Eval) infixl 8 "-"
| constant Code_Numeral.dup \<rightharpoonup>
    (SML) "IntInf.*/ (2,/ (_))"
    and (OCaml) "Z.shift'_left/ _/ 1"
    and (Haskell) "!(2 * _)"
    and (Scala) "!(2 * _)"
    and (Eval) "!(2 * _)"
| constant Code_Numeral.sub \<rightharpoonup>
    (SML) "!(raise/ Fail/ \"sub\")"
    and (OCaml) "failwith/ \"sub\""
    and (Haskell) "error/ \"sub\""
    and (Scala) "!sys.error(\"sub\")"
| constant "times :: integer \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (SML) "IntInf.* ((_), (_))"
    and (OCaml) "Z.mul"
    and (Haskell) infixl 7 "*"
    and (Scala) infixl 8 "*"
    and (Eval) infixl 9 "*"
| constant Code_Numeral.divmod_abs \<rightharpoonup>
    (SML) "IntInf.divMod/ (IntInf.abs _,/ IntInf.abs _)"
    and (OCaml) "!(fun k l ->/ if Z.equal Z.zero l then/ (Z.zero, l) else/ Z.div'_rem/ (Z.abs k)/ (Z.abs l))"
    and (Haskell) "divMod/ (abs _)/ (abs _)"
    and (Scala) "!((k: BigInt) => (l: BigInt) =>/ if (l == 0)/ (BigInt(0), k) else/ (k.abs '/% l.abs))"
    and (Eval) "Integer.div'_mod/ (abs _)/ (abs _)"
| constant "HOL.equal :: integer \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
    (SML) "!((_ : IntInf.int) = _)"
    and (OCaml) "Z.equal"
    and (Haskell) infix 4 "=="
    and (Scala) infixl 5 "=="
    and (Eval) infixl 6 "="
| constant "less_eq :: integer \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
    (SML) "IntInf.<= ((_), (_))"
    and (OCaml) "Z.leq"
    and (Haskell) infix 4 "<="
    and (Scala) infixl 4 "<="
    and (Eval) infixl 6 "<="
| constant "less :: integer \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
    (SML) "IntInf.< ((_), (_))"
    and (OCaml) "Z.lt"
    and (Haskell) infix 4 "<"
    and (Scala) infixl 4 "<"
    and (Eval) infixl 6 "<"
| constant "abs :: integer \<Rightarrow> _" \<rightharpoonup>
    (SML) "IntInf.abs"
    and (OCaml) "Z.abs"
    and (Haskell) "Prelude.abs"
    and (Scala) "_.abs"
    and (Eval) "abs"

code_identifier
  code_module Code_Numeral \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith


subsection \<open>Type of target language naturals\<close>

typedef natural = "UNIV :: nat set"
  morphisms nat_of_natural natural_of_nat ..

setup_lifting type_definition_natural

lemma natural_eq_iff [termination_simp]:
  "m = n \<longleftrightarrow> nat_of_natural m = nat_of_natural n"
  by transfer rule

lemma natural_eqI:
  "nat_of_natural m = nat_of_natural n \<Longrightarrow> m = n"
  using natural_eq_iff [of m n] by simp

lemma nat_of_natural_of_nat_inverse [simp]:
  "nat_of_natural (natural_of_nat n) = n"
  by transfer rule

lemma natural_of_nat_of_natural_inverse [simp]:
  "natural_of_nat (nat_of_natural n) = n"
  by transfer rule

instantiation natural :: "{comm_monoid_diff, semiring_1}"
begin

lift_definition zero_natural :: natural
  is "0 :: nat"
  .

declare zero_natural.rep_eq [simp]

lift_definition one_natural :: natural
  is "1 :: nat"
  .

declare one_natural.rep_eq [simp]

lift_definition plus_natural :: "natural \<Rightarrow> natural \<Rightarrow> natural"
  is "plus :: nat \<Rightarrow> nat \<Rightarrow> nat"
  .

declare plus_natural.rep_eq [simp]

lift_definition minus_natural :: "natural \<Rightarrow> natural \<Rightarrow> natural"
  is "minus :: nat \<Rightarrow> nat \<Rightarrow> nat"
  .

declare minus_natural.rep_eq [simp]

lift_definition times_natural :: "natural \<Rightarrow> natural \<Rightarrow> natural"
  is "times :: nat \<Rightarrow> nat \<Rightarrow> nat"
  .

declare times_natural.rep_eq [simp]

instance proof
qed (transfer, simp add: algebra_simps)+

end

instance natural :: Rings.dvd ..

context
  includes lifting_syntax
begin

lemma [transfer_rule]:
  \<open>(pcr_natural ===> pcr_natural ===> (\<longleftrightarrow>)) (dvd) (dvd)\<close>
  by (unfold dvd_def) transfer_prover

lemma [transfer_rule]:
  \<open>((\<longleftrightarrow>) ===> pcr_natural) of_bool of_bool\<close>
  by (unfold of_bool_def) transfer_prover

lemma [transfer_rule]:
  \<open>((=) ===> pcr_natural) (\<lambda>n. n) of_nat\<close>
proof -
  have "rel_fun HOL.eq pcr_natural (of_nat :: nat \<Rightarrow> nat) (of_nat :: nat \<Rightarrow> natural)"
    by (unfold of_nat_def) transfer_prover
  then show ?thesis by (simp add: id_def)
qed

lemma [transfer_rule]:
  \<open>((=) ===> pcr_natural) numeral numeral\<close>
proof -
  have \<open>((=) ===> pcr_natural) numeral (\<lambda>n. of_nat (numeral n))\<close>
    by transfer_prover
  then show ?thesis by simp
qed

lemma [transfer_rule]:
  \<open>(pcr_natural ===> (=) ===> pcr_natural) (^) (^)\<close>
  by (unfold power_def) transfer_prover

end

lemma nat_of_natural_of_nat [simp]:
  "nat_of_natural (of_nat n) = n"
  by transfer rule

lemma natural_of_nat_of_nat [simp, code_abbrev]:
  "natural_of_nat = of_nat"
  by transfer rule

lemma of_nat_of_natural [simp]:
  "of_nat (nat_of_natural n) = n"
  by transfer rule

lemma nat_of_natural_numeral [simp]:
  "nat_of_natural (numeral k) = numeral k"
  by transfer rule

instantiation natural :: "{linordered_semiring, equal}"
begin

lift_definition less_eq_natural :: "natural \<Rightarrow> natural \<Rightarrow> bool"
  is "less_eq :: nat \<Rightarrow> nat \<Rightarrow> bool"
  .

declare less_eq_natural.rep_eq [termination_simp]

lift_definition less_natural :: "natural \<Rightarrow> natural \<Rightarrow> bool"
  is "less :: nat \<Rightarrow> nat \<Rightarrow> bool"
  .

declare less_natural.rep_eq [termination_simp]

lift_definition equal_natural :: "natural \<Rightarrow> natural \<Rightarrow> bool"
  is "HOL.equal :: nat \<Rightarrow> nat \<Rightarrow> bool"
  .

instance proof
qed (transfer, simp add: algebra_simps equal less_le_not_le [symmetric] linear)+

end

context
  includes lifting_syntax
begin

lemma [transfer_rule]:
  \<open>(pcr_natural ===> pcr_natural ===> pcr_natural) min min\<close>
  by (unfold min_def) transfer_prover

lemma [transfer_rule]:
  \<open>(pcr_natural ===> pcr_natural ===> pcr_natural) max max\<close>
  by (unfold max_def) transfer_prover

end

lemma nat_of_natural_min [simp]:
  "nat_of_natural (min k l) = min (nat_of_natural k) (nat_of_natural l)"
  by transfer rule

lemma nat_of_natural_max [simp]:
  "nat_of_natural (max k l) = max (nat_of_natural k) (nat_of_natural l)"
  by transfer rule

instantiation natural :: unique_euclidean_semiring
begin

lift_definition divide_natural :: "natural \<Rightarrow> natural \<Rightarrow> natural"
  is "divide :: nat \<Rightarrow> nat \<Rightarrow> nat"
  .

declare divide_natural.rep_eq [simp]

lift_definition modulo_natural :: "natural \<Rightarrow> natural \<Rightarrow> natural"
  is "modulo :: nat \<Rightarrow> nat \<Rightarrow> nat"
  .

declare modulo_natural.rep_eq [simp]

lift_definition euclidean_size_natural :: "natural \<Rightarrow> nat"
  is "euclidean_size :: nat \<Rightarrow> nat"
  .

declare euclidean_size_natural.rep_eq [simp]

lift_definition division_segment_natural :: "natural \<Rightarrow> natural"
  is "division_segment :: nat \<Rightarrow> nat"
  .

declare division_segment_natural.rep_eq [simp]

instance
  by (standard; transfer)
    (auto simp add: algebra_simps unit_factor_nat_def gr0_conv_Suc)

end

lemma [code]:
  "euclidean_size = nat_of_natural"
  by (simp add: fun_eq_iff)

lemma [code]:
  "division_segment (n::natural) = 1"
  by (simp add: natural_eq_iff)

instance natural :: linordered_semidom
  by (standard; transfer) simp_all

instance natural :: unique_euclidean_semiring_with_nat
  by (standard; transfer) simp_all

instantiation natural :: semiring_bit_shifts
begin

lift_definition bit_natural :: \<open>natural \<Rightarrow> nat \<Rightarrow> bool\<close>
  is bit .

lift_definition push_bit_natural :: \<open>nat \<Rightarrow> natural \<Rightarrow> natural\<close>
  is push_bit .

lift_definition drop_bit_natural :: \<open>nat \<Rightarrow> natural \<Rightarrow> natural\<close>
  is drop_bit .

lift_definition take_bit_natural :: \<open>nat \<Rightarrow> natural \<Rightarrow> natural\<close>
  is take_bit .

instance by (standard; transfer)
  (fact bit_eq_rec bits_induct bit_iff_odd push_bit_eq_mult drop_bit_eq_div take_bit_eq_mod
    bits_div_0 bits_div_by_1 bits_mod_div_trivial even_succ_div_2
    exp_div_exp_eq div_exp_eq mod_exp_eq mult_exp_mod_exp_eq div_exp_mod_exp_eq
    even_mask_div_iff even_mult_exp_div_exp_iff)+

end

instance natural :: unique_euclidean_semiring_with_bit_shifts ..

lemma [code]:
  \<open>bit m n \<longleftrightarrow> odd (drop_bit n m)\<close>
  \<open>push_bit n m = m * 2 ^ n\<close>
  \<open>drop_bit n m = m div 2 ^ n\<close>
  \<open>take_bit n m = m mod 2 ^ n\<close> for m :: natural
  by (fact bit_iff_odd_drop_bit push_bit_eq_mult drop_bit_eq_div take_bit_eq_mod)+

lift_definition natural_of_integer :: "integer \<Rightarrow> natural"
  is "nat :: int \<Rightarrow> nat"
  .

lift_definition integer_of_natural :: "natural \<Rightarrow> integer"
  is "of_nat :: nat \<Rightarrow> int"
  .

lemma natural_of_integer_of_natural [simp]:
  "natural_of_integer (integer_of_natural n) = n"
  by transfer simp

lemma integer_of_natural_of_integer [simp]:
  "integer_of_natural (natural_of_integer k) = max 0 k"
  by transfer auto

lemma int_of_integer_of_natural [simp]:
  "int_of_integer (integer_of_natural n) = of_nat (nat_of_natural n)"
  by transfer rule

lemma integer_of_natural_of_nat [simp]:
  "integer_of_natural (of_nat n) = of_nat n"
  by transfer rule

lemma [measure_function]:
  "is_measure nat_of_natural"
  by (rule is_measure_trivial)


subsection \<open>Inductive representation of target language naturals\<close>

lift_definition Suc :: "natural \<Rightarrow> natural"
  is Nat.Suc
  .

declare Suc.rep_eq [simp]

old_rep_datatype "0::natural" Suc
  by (transfer, fact nat.induct nat.inject nat.distinct)+

lemma natural_cases [case_names nat, cases type: natural]:
  fixes m :: natural
  assumes "\<And>n. m = of_nat n \<Longrightarrow> P"
  shows P
  using assms by transfer blast

instantiation natural :: size
begin

definition size_nat where [simp, code]: "size_nat = nat_of_natural"

instance ..

end

lemma natural_decr [termination_simp]:
  "n \<noteq> 0 \<Longrightarrow> nat_of_natural n - Nat.Suc 0 < nat_of_natural n"
  by transfer simp

lemma natural_zero_minus_one: "(0::natural) - 1 = 0"
  by (rule zero_diff)

lemma Suc_natural_minus_one: "Suc n - 1 = n"
  by transfer simp

hide_const (open) Suc


subsection \<open>Code refinement for target language naturals\<close>

lift_definition Nat :: "integer \<Rightarrow> natural"
  is nat
  .

lemma [code_post]:
  "Nat 0 = 0"
  "Nat 1 = 1"
  "Nat (numeral k) = numeral k"
  by (transfer, simp)+

lemma [code abstype]:
  "Nat (integer_of_natural n) = n"
  by transfer simp

lemma [code]:
  "natural_of_nat n = natural_of_integer (integer_of_nat n)"
  by transfer simp

lemma [code abstract]:
  "integer_of_natural (natural_of_integer k) = max 0 k"
  by simp

lemma [code_abbrev]:
  "natural_of_integer (Code_Numeral.Pos k) = numeral k"
  by transfer simp

lemma [code abstract]:
  "integer_of_natural 0 = 0"
  by transfer simp

lemma [code abstract]:
  "integer_of_natural 1 = 1"
  by transfer simp

lemma [code abstract]:
  "integer_of_natural (Code_Numeral.Suc n) = integer_of_natural n + 1"
  by transfer simp

lemma [code]:
  "nat_of_natural = nat_of_integer \<circ> integer_of_natural"
  by transfer (simp add: fun_eq_iff)

lemma [code, code_unfold]:
  "case_natural f g n = (if n = 0 then f else g (n - 1))"
  by (cases n rule: natural.exhaust) (simp_all, simp add: Suc_def)

declare natural.rec [code del]

lemma [code abstract]:
  "integer_of_natural (m + n) = integer_of_natural m + integer_of_natural n"
  by transfer simp

lemma [code abstract]:
  "integer_of_natural (m - n) = max 0 (integer_of_natural m - integer_of_natural n)"
  by transfer simp

lemma [code abstract]:
  "integer_of_natural (m * n) = integer_of_natural m * integer_of_natural n"
  by transfer simp

lemma [code abstract]:
  "integer_of_natural (m div n) = integer_of_natural m div integer_of_natural n"
  by transfer (simp add: zdiv_int)

lemma [code abstract]:
  "integer_of_natural (m mod n) = integer_of_natural m mod integer_of_natural n"
  by transfer (simp add: zmod_int)

lemma [code]:
  "HOL.equal m n \<longleftrightarrow> HOL.equal (integer_of_natural m) (integer_of_natural n)"
  by transfer (simp add: equal)

lemma [code nbe]: "HOL.equal n (n::natural) \<longleftrightarrow> True"
  by (rule equal_class.equal_refl)

lemma [code]: "m \<le> n \<longleftrightarrow> integer_of_natural m \<le> integer_of_natural n"
  by transfer simp

lemma [code]: "m < n \<longleftrightarrow> integer_of_natural m < integer_of_natural n"
  by transfer simp

hide_const (open) Nat

code_reflect Code_Numeral
  datatypes natural
  functions "Code_Numeral.Suc" "0 :: natural" "1 :: natural"
    "plus :: natural \<Rightarrow> _" "minus :: natural \<Rightarrow> _"
    "times :: natural \<Rightarrow> _" "divide :: natural \<Rightarrow> _"
    "modulo :: natural \<Rightarrow> _"
    integer_of_natural natural_of_integer


subsection \<open>Bit operations\<close>

instantiation integer :: ring_bit_operations
begin

lift_definition not_integer :: \<open>integer \<Rightarrow> integer\<close>
  is not .

lift_definition and_integer :: \<open>integer \<Rightarrow> integer \<Rightarrow> integer\<close>
  is \<open>and\<close> .

lift_definition or_integer :: \<open>integer \<Rightarrow> integer \<Rightarrow> integer\<close>
  is or .

lift_definition xor_integer ::  \<open>integer \<Rightarrow> integer \<Rightarrow> integer\<close>
  is xor .

lift_definition mask_integer :: \<open>nat \<Rightarrow> integer\<close>
  is mask .

lift_definition set_bit_integer :: \<open>nat \<Rightarrow> integer \<Rightarrow> integer\<close>
  is set_bit .

lift_definition unset_bit_integer :: \<open>nat \<Rightarrow> integer \<Rightarrow> integer\<close>
  is unset_bit .

lift_definition flip_bit_integer :: \<open>nat \<Rightarrow> integer \<Rightarrow> integer\<close>
  is flip_bit .

instance by (standard; transfer)
  (simp_all add: minus_eq_not_minus_1 mask_eq_exp_minus_1
    bit_not_iff bit_and_iff bit_or_iff bit_xor_iff
    set_bit_def bit_unset_bit_iff flip_bit_def)

end

lemma [code]:
  \<open>mask n = 2 ^ n - (1::integer)\<close>
  by (simp add: mask_eq_exp_minus_1)

instantiation natural :: semiring_bit_operations
begin

lift_definition and_natural :: \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is \<open>and\<close> .

lift_definition or_natural :: \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is or .

lift_definition xor_natural ::  \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is xor .

lift_definition mask_natural :: \<open>nat \<Rightarrow> natural\<close>
  is mask .

lift_definition set_bit_natural :: \<open>nat \<Rightarrow> natural \<Rightarrow> natural\<close>
  is set_bit .

lift_definition unset_bit_natural :: \<open>nat \<Rightarrow> natural \<Rightarrow> natural\<close>
  is unset_bit .

lift_definition flip_bit_natural :: \<open>nat \<Rightarrow> natural \<Rightarrow> natural\<close>
  is flip_bit .

instance by (standard; transfer)
  (simp_all add: mask_eq_exp_minus_1
    bit_and_iff bit_or_iff bit_xor_iff
    set_bit_def bit_unset_bit_iff flip_bit_def)

end

lemma [code]:
  \<open>integer_of_natural (mask n) = mask n\<close>
  by transfer (simp add: mask_eq_exp_minus_1 of_nat_diff)


lifting_update integer.lifting
lifting_forget integer.lifting

lifting_update natural.lifting
lifting_forget natural.lifting

end
