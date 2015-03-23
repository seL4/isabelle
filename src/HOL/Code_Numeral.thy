(*  Title:      HOL/Code_Numeral.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section {* Numeric types for code generation onto target language numerals only *}

theory Code_Numeral
imports Nat_Transfer Divides Lifting
begin

subsection {* Type of target language integers *}

typedef integer = "UNIV \<Colon> int set"
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

lemma [transfer_rule]:
  "rel_fun HOL.eq pcr_integer (of_nat :: nat \<Rightarrow> int) (of_nat :: nat \<Rightarrow> integer)"
  by (unfold of_nat_def [abs_def]) transfer_prover

lemma [transfer_rule]:
  "rel_fun HOL.eq pcr_integer (\<lambda>k :: int. k :: int) (of_int :: int \<Rightarrow> integer)"
proof -
  have "rel_fun HOL.eq pcr_integer (of_int :: int \<Rightarrow> int) (of_int :: int \<Rightarrow> integer)"
    by (unfold of_int_of_nat [abs_def]) transfer_prover
  then show ?thesis by (simp add: id_def)
qed

lemma [transfer_rule]:
  "rel_fun HOL.eq pcr_integer (numeral :: num \<Rightarrow> int) (numeral :: num \<Rightarrow> integer)"
proof -
  have "rel_fun HOL.eq pcr_integer (numeral :: num \<Rightarrow> int) (\<lambda>n. of_int (numeral n))"
    by transfer_prover
  then show ?thesis by simp
qed

lemma [transfer_rule]:
  "rel_fun HOL.eq (rel_fun HOL.eq pcr_integer) (Num.sub :: _ \<Rightarrow> _ \<Rightarrow> int) (Num.sub :: _ \<Rightarrow> _ \<Rightarrow> integer)"
  by (unfold Num.sub_def [abs_def]) transfer_prover

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

instantiation integer :: "{ring_div, equal, linordered_idom}"
begin

lift_definition div_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer"
  is "Divides.div :: int \<Rightarrow> int \<Rightarrow> int"
  .

declare div_integer.rep_eq [simp]

lift_definition mod_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer"
  is "Divides.mod :: int \<Rightarrow> int \<Rightarrow> int"
  .

declare mod_integer.rep_eq [simp]

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

lift_definition less_integer :: "integer \<Rightarrow> integer \<Rightarrow> bool"
  is "less :: int \<Rightarrow> int \<Rightarrow> bool"
  .

lift_definition equal_integer :: "integer \<Rightarrow> integer \<Rightarrow> bool"
  is "HOL.equal :: int \<Rightarrow> int \<Rightarrow> bool"
  .

instance proof
qed (transfer, simp add: algebra_simps equal less_le_not_le [symmetric] mult_strict_right_mono linear)+

end

lemma [transfer_rule]:
  "rel_fun pcr_integer (rel_fun pcr_integer pcr_integer) (min :: _ \<Rightarrow> _ \<Rightarrow> int) (min :: _ \<Rightarrow> _ \<Rightarrow> integer)"
  by (unfold min_def [abs_def]) transfer_prover

lemma [transfer_rule]:
  "rel_fun pcr_integer (rel_fun pcr_integer pcr_integer) (max :: _ \<Rightarrow> _ \<Rightarrow> int) (max :: _ \<Rightarrow> _ \<Rightarrow> integer)"
  by (unfold max_def [abs_def]) transfer_prover

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

instance integer :: semiring_numeral_div
  by intro_classes (transfer,
    fact semiring_numeral_div_class.le_add_diff_inverse2
    semiring_numeral_div_class.div_less
    semiring_numeral_div_class.mod_less
    semiring_numeral_div_class.div_positive
    semiring_numeral_div_class.mod_less_eq_dividend
    semiring_numeral_div_class.pos_mod_bound
    semiring_numeral_div_class.pos_mod_sign
    semiring_numeral_div_class.mod_mult2_eq
    semiring_numeral_div_class.div_mult2_eq
    semiring_numeral_div_class.discrete)+

lemma integer_of_nat_0: "integer_of_nat 0 = 0"
by transfer simp

lemma integer_of_nat_1: "integer_of_nat 1 = 1"
by transfer simp

lemma integer_of_nat_numeral:
  "integer_of_nat (numeral n) = numeral n"
by transfer simp

subsection {* Code theorems for target language integers *}

text {* Constructors *}

definition Pos :: "num \<Rightarrow> integer"
where
  [simp, code_abbrev]: "Pos = numeral"

lemma [transfer_rule]:
  "rel_fun HOL.eq pcr_integer numeral Pos"
  by simp transfer_prover

definition Neg :: "num \<Rightarrow> integer"
where
  [simp, code_abbrev]: "Neg n = - Pos n"

lemma [transfer_rule]:
  "rel_fun HOL.eq pcr_integer (\<lambda>n. - numeral n) Neg"
  by (simp add: Neg_def [abs_def]) transfer_prover

code_datatype "0::integer" Pos Neg


text {* Auxiliary operations *}

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


text {* Implementations *}

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

lemma fst_divmod [simp]:
  "fst (divmod_integer k l) = k div l"
  by (simp add: divmod_integer_def)

lemma snd_divmod [simp]:
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

lemma divmod_integer_code [code]:
  "divmod_integer k l =
    (if k = 0 then (0, 0) else if l = 0 then (0, k) else
    (apsnd \<circ> times \<circ> sgn) l (if sgn k = sgn l
      then divmod_abs k l
      else (let (r, s) = divmod_abs k l in
        if s = 0 then (- r, 0) else (- r - 1, \<bar>l\<bar> - s))))"
proof -
  have aux1: "\<And>k l::int. sgn k = sgn l \<longleftrightarrow> k = 0 \<and> l = 0 \<or> 0 < l \<and> 0 < k \<or> l < 0 \<and> k < 0"
    by (auto simp add: sgn_if)
  have aux2: "\<And>q::int. - int_of_integer k = int_of_integer l * q \<longleftrightarrow> int_of_integer k = int_of_integer l * - q" by auto
  show ?thesis
    by (simp add: prod_eq_iff integer_eq_iff case_prod_beta aux1)
      (auto simp add: zdiv_zminus1_eq_if zmod_zminus1_eq_if div_minus_right mod_minus_right aux2)
qed

lemma div_integer_code [code]:
  "k div l = fst (divmod_integer k l)"
  by simp

lemma mod_integer_code [code]:
  "k mod l = snd (divmod_integer k l)"
  by simp

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

lift_definition integer_of_num :: "num \<Rightarrow> integer"
  is "numeral :: num \<Rightarrow> int"
  .

lemma integer_of_num [code]:
  "integer_of_num num.One = 1"
  "integer_of_num (num.Bit0 n) = (let k = integer_of_num n in k + k)"
  "integer_of_num (num.Bit1 n) = (let k = integer_of_num n in k + k + 1)"
  by (transfer, simp only: numeral.simps Let_def)+

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
  obtain j where "k = integer_of_int j"
  proof
    show "k = integer_of_int (int_of_integer k)" by simp
  qed
  moreover have "2 * (j div 2) = j - j mod 2"
    by (simp add: zmult_div_cancel mult.commute)
  ultimately show ?thesis
    by (auto simp add: split_def Let_def mod_integer_def nat_of_integer_def not_le
      nat_add_distrib [symmetric] Suc_nat_eq_nat_zadd1)
      (auto simp add: mult_2 [symmetric])
qed

lemma int_of_integer_code [code]:
  "int_of_integer k = (if k < 0 then - (int_of_integer (- k))
     else if k = 0 then 0
     else let
       (l, j) = divmod_integer k 2;
       l' = 2 * int_of_integer l
     in if j = 0 then l' else l' + 1)"
  by (auto simp add: split_def Let_def integer_eq_iff zmult_div_cancel)

lemma integer_of_int_code [code]:
  "integer_of_int k = (if k < 0 then - (integer_of_int (- k))
     else if k = 0 then 0
     else let
       (l, j) = divmod_int k 2;
       l' = 2 * integer_of_int l
     in if j = 0 then l' else l' + 1)"
  by (auto simp add: split_def Let_def integer_eq_iff zmult_div_cancel)

hide_const (open) Pos Neg sub dup divmod_abs


subsection {* Serializer setup for target language integers *}

code_reserved Eval int Integer abs

code_printing
  type_constructor integer \<rightharpoonup>
    (SML) "IntInf.int"
    and (OCaml) "Big'_int.big'_int"
    and (Haskell) "Integer"
    and (Scala) "BigInt"
    and (Eval) "int"
| class_instance integer :: equal \<rightharpoonup>
    (Haskell) -

code_printing
  constant "0::integer" \<rightharpoonup>
    (SML) "!(0/ :/ IntInf.int)"
    and (OCaml) "Big'_int.zero'_big'_int"
    and (Haskell) "!(0/ ::/ Integer)"
    and (Scala) "BigInt(0)"

setup {*
  fold (fn target =>
    Numeral.add_code @{const_name Code_Numeral.Pos} I Code_Printer.literal_numeral target
    #> Numeral.add_code @{const_name Code_Numeral.Neg} (op ~) Code_Printer.literal_numeral target)
    ["SML", "OCaml", "Haskell", "Scala"]
*}

code_printing
  constant "plus :: integer \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (SML) "IntInf.+ ((_), (_))"
    and (OCaml) "Big'_int.add'_big'_int"
    and (Haskell) infixl 6 "+"
    and (Scala) infixl 7 "+"
    and (Eval) infixl 8 "+"
| constant "uminus :: integer \<Rightarrow> _" \<rightharpoonup>
    (SML) "IntInf.~"
    and (OCaml) "Big'_int.minus'_big'_int"
    and (Haskell) "negate"
    and (Scala) "!(- _)"
    and (Eval) "~/ _"
| constant "minus :: integer \<Rightarrow> _" \<rightharpoonup>
    (SML) "IntInf.- ((_), (_))"
    and (OCaml) "Big'_int.sub'_big'_int"
    and (Haskell) infixl 6 "-"
    and (Scala) infixl 7 "-"
    and (Eval) infixl 8 "-"
| constant Code_Numeral.dup \<rightharpoonup>
    (SML) "IntInf.*/ (2,/ (_))"
    and (OCaml) "Big'_int.mult'_big'_int/ (Big'_int.big'_int'_of'_int/ 2)"
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
    and (OCaml) "Big'_int.mult'_big'_int"
    and (Haskell) infixl 7 "*"
    and (Scala) infixl 8 "*"
    and (Eval) infixl 9 "*"
| constant Code_Numeral.divmod_abs \<rightharpoonup>
    (SML) "IntInf.divMod/ (IntInf.abs _,/ IntInf.abs _)"
    and (OCaml) "Big'_int.quomod'_big'_int/ (Big'_int.abs'_big'_int _)/ (Big'_int.abs'_big'_int _)"
    and (Haskell) "divMod/ (abs _)/ (abs _)"
    and (Scala) "!((k: BigInt) => (l: BigInt) =>/ if (l == 0)/ (BigInt(0), k) else/ (k.abs '/% l.abs))"
    and (Eval) "Integer.div'_mod/ (abs _)/ (abs _)"
| constant "HOL.equal :: integer \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
    (SML) "!((_ : IntInf.int) = _)"
    and (OCaml) "Big'_int.eq'_big'_int"
    and (Haskell) infix 4 "=="
    and (Scala) infixl 5 "=="
    and (Eval) infixl 6 "="
| constant "less_eq :: integer \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
    (SML) "IntInf.<= ((_), (_))"
    and (OCaml) "Big'_int.le'_big'_int"
    and (Haskell) infix 4 "<="
    and (Scala) infixl 4 "<="
    and (Eval) infixl 6 "<="
| constant "less :: integer \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
    (SML) "IntInf.< ((_), (_))"
    and (OCaml) "Big'_int.lt'_big'_int"
    and (Haskell) infix 4 "<"
    and (Scala) infixl 4 "<"
    and (Eval) infixl 6 "<"

code_identifier
  code_module Code_Numeral \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith


subsection {* Type of target language naturals *}

typedef natural = "UNIV \<Colon> nat set"
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

lemma [transfer_rule]:
  "rel_fun HOL.eq pcr_natural (\<lambda>n::nat. n) (of_nat :: nat \<Rightarrow> natural)"
proof -
  have "rel_fun HOL.eq pcr_natural (of_nat :: nat \<Rightarrow> nat) (of_nat :: nat \<Rightarrow> natural)"
    by (unfold of_nat_def [abs_def]) transfer_prover
  then show ?thesis by (simp add: id_def)
qed

lemma [transfer_rule]:
  "rel_fun HOL.eq pcr_natural (numeral :: num \<Rightarrow> nat) (numeral :: num \<Rightarrow> natural)"
proof -
  have "rel_fun HOL.eq pcr_natural (numeral :: num \<Rightarrow> nat) (\<lambda>n. of_nat (numeral n))"
    by transfer_prover
  then show ?thesis by simp
qed

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

instantiation natural :: "{semiring_div, equal, linordered_semiring}"
begin

lift_definition div_natural :: "natural \<Rightarrow> natural \<Rightarrow> natural"
  is "Divides.div :: nat \<Rightarrow> nat \<Rightarrow> nat"
  .

declare div_natural.rep_eq [simp]

lift_definition mod_natural :: "natural \<Rightarrow> natural \<Rightarrow> natural"
  is "Divides.mod :: nat \<Rightarrow> nat \<Rightarrow> nat"
  .

declare mod_natural.rep_eq [simp]

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

lemma [transfer_rule]:
  "rel_fun pcr_natural (rel_fun pcr_natural pcr_natural) (min :: _ \<Rightarrow> _ \<Rightarrow> nat) (min :: _ \<Rightarrow> _ \<Rightarrow> natural)"
  by (unfold min_def [abs_def]) transfer_prover

lemma [transfer_rule]:
  "rel_fun pcr_natural (rel_fun pcr_natural pcr_natural) (max :: _ \<Rightarrow> _ \<Rightarrow> nat) (max :: _ \<Rightarrow> _ \<Rightarrow> natural)"
  by (unfold max_def [abs_def]) transfer_prover

lemma nat_of_natural_min [simp]:
  "nat_of_natural (min k l) = min (nat_of_natural k) (nat_of_natural l)"
  by transfer rule

lemma nat_of_natural_max [simp]:
  "nat_of_natural (max k l) = max (nat_of_natural k) (nat_of_natural l)"
  by transfer rule

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


subsection {* Inductive representation of target language naturals *}

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

lemma [simp, code]: "size_natural = nat_of_natural"
proof (rule ext)
  fix n
  show "size_natural n = nat_of_natural n"
    by (induct n) simp_all
qed

lemma [simp, code]: "size = nat_of_natural"
proof (rule ext)
  fix n
  show "size n = nat_of_natural n"
    by (induct n) simp_all
qed

lemma natural_decr [termination_simp]:
  "n \<noteq> 0 \<Longrightarrow> nat_of_natural n - Nat.Suc 0 < nat_of_natural n"
  by transfer simp

lemma natural_zero_minus_one: "(0::natural) - 1 = 0"
  by (rule zero_diff)

lemma Suc_natural_minus_one: "Suc n - 1 = n"
  by transfer simp

hide_const (open) Suc


subsection {* Code refinement for target language naturals *}

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

lemma [code abstract]:
  "integer_of_natural (natural_of_nat n) = of_nat n"
  by simp

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
  by transfer (simp add: of_nat_mult)

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

lifting_update integer.lifting
lifting_forget integer.lifting

lifting_update natural.lifting
lifting_forget natural.lifting

code_reflect Code_Numeral
  datatypes natural = _
  functions integer_of_natural natural_of_integer

end
