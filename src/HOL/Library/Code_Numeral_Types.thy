(*  Title:      HOL/Library/Code_Numeral_Types.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Numeric types for code generation onto target language numerals only *}

theory Code_Numeral_Types
imports Main Nat_Transfer Divides Lifting
begin

subsection {* Type of target language integers *}

typedef integer = "UNIV \<Colon> int set"
  morphisms int_of_integer integer_of_int ..

lemma integer_eq_iff:
  "k = l \<longleftrightarrow> int_of_integer k = int_of_integer l"
  using int_of_integer_inject [of k l] ..

lemma integer_eqI:
  "int_of_integer k = int_of_integer l \<Longrightarrow> k = l"
  using integer_eq_iff [of k l] by simp

lemma int_of_integer_integer_of_int [simp]:
  "int_of_integer (integer_of_int k) = k"
  using integer_of_int_inverse [of k] by simp

lemma integer_of_int_int_of_integer [simp]:
  "integer_of_int (int_of_integer k) = k"
  using int_of_integer_inverse [of k] by simp

instantiation integer :: ring_1
begin

definition
  "0 = integer_of_int 0"

lemma int_of_integer_zero [simp]:
  "int_of_integer 0 = 0"
  by (simp add: zero_integer_def)

definition
  "1 = integer_of_int 1"

lemma int_of_integer_one [simp]:
  "int_of_integer 1 = 1"
  by (simp add: one_integer_def)

definition
  "k + l = integer_of_int (int_of_integer k + int_of_integer l)"

lemma int_of_integer_plus [simp]:
  "int_of_integer (k + l) = int_of_integer k + int_of_integer l"
  by (simp add: plus_integer_def)

definition
  "- k = integer_of_int (- int_of_integer k)"

lemma int_of_integer_uminus [simp]:
  "int_of_integer (- k) = - int_of_integer k"
  by (simp add: uminus_integer_def)

definition
  "k - l = integer_of_int (int_of_integer k - int_of_integer l)"

lemma int_of_integer_minus [simp]:
  "int_of_integer (k - l) = int_of_integer k - int_of_integer l"
  by (simp add: minus_integer_def)

definition
  "k * l = integer_of_int (int_of_integer k * int_of_integer l)"

lemma int_of_integer_times [simp]:
  "int_of_integer (k * l) = int_of_integer k * int_of_integer l"
  by (simp add: times_integer_def)

instance proof
qed (auto simp add: integer_eq_iff algebra_simps)

end

lemma int_of_integer_of_nat [simp]:
  "int_of_integer (of_nat n) = of_nat n"
  by (induct n) simp_all

definition nat_of_integer :: "integer \<Rightarrow> nat"
where
  "nat_of_integer k = Int.nat (int_of_integer k)"

lemma nat_of_integer_of_nat [simp]:
  "nat_of_integer (of_nat n) = n"
  by (simp add: nat_of_integer_def)

lemma int_of_integer_of_int [simp]:
  "int_of_integer (of_int k) = k"
  by (induct k) (simp_all, simp only: neg_numeral_def numeral_One int_of_integer_uminus int_of_integer_one)

lemma integer_integer_of_int_eq_of_integer_integer_of_int [simp, code_abbrev]:
  "integer_of_int = of_int"
  by rule (simp add: integer_eq_iff)

lemma of_int_integer_of [simp]:
  "of_int (int_of_integer k) = (k :: integer)"
  by (simp add: integer_eq_iff)

lemma int_of_integer_numeral [simp]:
  "int_of_integer (numeral k) = numeral k"
  using int_of_integer_of_int [of "numeral k"] by simp

lemma int_of_integer_neg_numeral [simp]:
  "int_of_integer (neg_numeral k) = neg_numeral k"
  by (simp only: neg_numeral_def int_of_integer_uminus) simp

lemma int_of_integer_sub [simp]:
  "int_of_integer (Num.sub k l) = Num.sub k l"
  by (simp only: Num.sub_def int_of_integer_minus int_of_integer_numeral)

instantiation integer :: "{ring_div, equal, linordered_idom}"
begin

definition
  "k div l = of_int (int_of_integer k div int_of_integer l)"

lemma int_of_integer_div [simp]:
  "int_of_integer (k div l) = int_of_integer k div int_of_integer l"
  by (simp add: div_integer_def)

definition
  "k mod l = of_int (int_of_integer k mod int_of_integer l)"

lemma int_of_integer_mod [simp]:
  "int_of_integer (k mod l) = int_of_integer k mod int_of_integer l"
  by (simp add: mod_integer_def)

definition
  "\<bar>k\<bar> = of_int \<bar>int_of_integer k\<bar>"

lemma int_of_integer_abs [simp]:
  "int_of_integer \<bar>k\<bar> = \<bar>int_of_integer k\<bar>"
  by (simp add: abs_integer_def)

definition
  "sgn k = of_int (sgn (int_of_integer k))"

lemma int_of_integer_sgn [simp]:
  "int_of_integer (sgn k) = sgn (int_of_integer k)"
  by (simp add: sgn_integer_def)

definition
  "k \<le> l \<longleftrightarrow> int_of_integer k \<le> int_of_integer l"

definition
  "k < l \<longleftrightarrow> int_of_integer k < int_of_integer l"

definition
  "HOL.equal k l \<longleftrightarrow> HOL.equal (int_of_integer k) (int_of_integer l)"

instance proof
qed (auto simp add: integer_eq_iff algebra_simps
  less_eq_integer_def less_integer_def equal_integer_def equal
  intro: mult_strict_right_mono)

end

lemma int_of_integer_min [simp]:
  "int_of_integer (min k l) = min (int_of_integer k) (int_of_integer l)"
  by (simp add: min_def less_eq_integer_def)

lemma int_of_integer_max [simp]:
  "int_of_integer (max k l) = max (int_of_integer k) (int_of_integer l)"
  by (simp add: max_def less_eq_integer_def)

lemma nat_of_integer_non_positive [simp]:
  "k \<le> 0 \<Longrightarrow> nat_of_integer k = 0"
  by (simp add: nat_of_integer_def less_eq_integer_def)

lemma of_nat_of_integer [simp]:
  "of_nat (nat_of_integer k) = max 0 k"
  by (simp add: nat_of_integer_def integer_eq_iff less_eq_integer_def max_def)


subsection {* Code theorems for target language integers *}

text {* Constructors *}

definition Pos :: "num \<Rightarrow> integer"
where
  [simp, code_abbrev]: "Pos = numeral"

definition Neg :: "num \<Rightarrow> integer"
where
  [simp, code_abbrev]: "Neg = neg_numeral"

code_datatype "0::integer" Pos Neg


text {* Auxiliary operations *}

definition dup :: "integer \<Rightarrow> integer"
where
  [simp]: "dup k = k + k"

lemma dup_code [code]:
  "dup 0 = 0"
  "dup (Pos n) = Pos (Num.Bit0 n)"
  "dup (Neg n) = Neg (Num.Bit0 n)"
  unfolding Pos_def Neg_def neg_numeral_def
  by (simp_all add: numeral_Bit0)

definition sub :: "num \<Rightarrow> num \<Rightarrow> integer"
where
  [simp]: "sub m n = numeral m - numeral n"

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
  unfolding sub_def dup_def numeral.simps Pos_def Neg_def
    neg_numeral_def numeral_BitM
  by (simp_all only: algebra_simps add.comm_neutral)


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
  by simp_all

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
  by simp_all

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

lemma divmod_abs_terminate_code [code]:
  "divmod_abs (Neg k) (Neg l) = divmod_abs (Pos k) (Pos l)"
  "divmod_abs (Neg k) (Pos l) = divmod_abs (Pos k) (Pos l)"
  "divmod_abs (Pos k) (Neg l) = divmod_abs (Pos k) (Pos l)"
  "divmod_abs j 0 = (0, \<bar>j\<bar>)"
  "divmod_abs 0 j = (0, 0)"
  by (simp_all add: prod_eq_iff)

lemma divmod_abs_rec_code [code]:
  "divmod_abs (Pos k) (Pos l) =
    (let j = sub k l in
       if j < 0 then (0, Pos k)
       else let (q, r) = divmod_abs j (Pos l) in (q + 1, r))"
  by (auto simp add: prod_eq_iff integer_eq_iff Let_def prod_case_beta
    sub_non_negative sub_negative div_pos_pos_trivial mod_pos_pos_trivial div_pos_geq mod_pos_geq)

lemma divmod_integer_code [code]: "divmod_integer k l =
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
    by (simp add: prod_eq_iff integer_eq_iff prod_case_beta aux1)
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
  by (simp_all add: equal integer_eq_iff)

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
  by (simp_all add: less_eq_integer_def)

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
  by (simp_all add: less_integer_def)

definition integer_of_num :: "num \<Rightarrow> integer"
where
  "integer_of_num = numeral"

lemma integer_of_num [code]:
  "integer_of_num num.One = 1"
  "integer_of_num (num.Bit0 n) = (let k = integer_of_num n in k + k)"
  "integer_of_num (num.Bit1 n) = (let k = integer_of_num n in k + k + 1)"
  by (simp_all only: Let_def) (simp_all only: integer_of_num_def numeral.simps)

definition num_of_integer :: "integer \<Rightarrow> num"
where
  "num_of_integer = num_of_nat \<circ> nat_of_integer"

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
    by (auto simp add: num_of_integer_def nat_of_integer_def Let_def prod_case_beta
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
    by (simp add: zmult_div_cancel mult_commute)
  ultimately show ?thesis
    by (auto simp add: split_def Let_def mod_integer_def nat_of_integer_def not_le
      nat_add_distrib [symmetric] Suc_nat_eq_nat_zadd1)
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

code_reserved Eval abs

code_type integer
  (SML "IntInf.int")
  (OCaml "Big'_int.big'_int")
  (Haskell "Integer")
  (Scala "BigInt")
  (Eval "int")

code_instance integer :: equal
  (Haskell -)

code_const "0::integer"
  (SML "0")
  (OCaml "Big'_int.zero'_big'_int")
  (Haskell "0")
  (Scala "BigInt(0)")

setup {*
  fold (Numeral.add_code @{const_name Code_Numeral_Types.Pos}
    false Code_Printer.literal_numeral) ["SML", "OCaml", "Haskell", "Scala"]
*}

setup {*
  fold (Numeral.add_code @{const_name Code_Numeral_Types.Neg}
    true Code_Printer.literal_numeral) ["SML", "OCaml", "Haskell", "Scala"]
*}

code_const "plus :: integer \<Rightarrow> _ \<Rightarrow> _"
  (SML "IntInf.+ ((_), (_))")
  (OCaml "Big'_int.add'_big'_int")
  (Haskell infixl 6 "+")
  (Scala infixl 7 "+")
  (Eval infixl 8 "+")

code_const "uminus :: integer \<Rightarrow> _"
  (SML "IntInf.~")
  (OCaml "Big'_int.minus'_big'_int")
  (Haskell "negate")
  (Scala "!(- _)")
  (Eval "~/ _")

code_const "minus :: integer \<Rightarrow> _"
  (SML "IntInf.- ((_), (_))")
  (OCaml "Big'_int.sub'_big'_int")
  (Haskell infixl 6 "-")
  (Scala infixl 7 "-")
  (Eval infixl 8 "-")

code_const Code_Numeral_Types.dup
  (SML "IntInf.*/ (2,/ (_))")
  (OCaml "Big'_int.mult'_big'_int/ (Big'_int.big'_int'_of'_int/ 2)")
  (Haskell "!(2 * _)")
  (Scala "!(2 * _)")
  (Eval "!(2 * _)")

code_const Code_Numeral_Types.sub
  (SML "!(raise/ Fail/ \"sub\")")
  (OCaml "failwith/ \"sub\"")
  (Haskell "error/ \"sub\"")
  (Scala "!sys.error(\"sub\")")

code_const "times :: integer \<Rightarrow> _ \<Rightarrow> _"
  (SML "IntInf.* ((_), (_))")
  (OCaml "Big'_int.mult'_big'_int")
  (Haskell infixl 7 "*")
  (Scala infixl 8 "*")
  (Eval infixl 9 "*")

code_const Code_Numeral_Types.divmod_abs
  (SML "IntInf.divMod/ (IntInf.abs _,/ IntInf.abs _)")
  (OCaml "Big'_int.quomod'_big'_int/ (Big'_int.abs'_big'_int _)/ (Big'_int.abs'_big'_int _)")
  (Haskell "divMod/ (abs _)/ (abs _)")
  (Scala "!((k: BigInt) => (l: BigInt) =>/ if (l == 0)/ (BigInt(0), k) else/ (k.abs '/% l.abs))")
  (Eval "Integer.div'_mod/ (abs _)/ (abs _)")

code_const "HOL.equal :: integer \<Rightarrow> _ \<Rightarrow> bool"
  (SML "!((_ : IntInf.int) = _)")
  (OCaml "Big'_int.eq'_big'_int")
  (Haskell infix 4 "==")
  (Scala infixl 5 "==")
  (Eval infixl 6 "=")

code_const "less_eq :: integer \<Rightarrow> _ \<Rightarrow> bool"
  (SML "IntInf.<= ((_), (_))")
  (OCaml "Big'_int.le'_big'_int")
  (Haskell infix 4 "<=")
  (Scala infixl 4 "<=")
  (Eval infixl 6 "<=")

code_const "less :: integer \<Rightarrow> _ \<Rightarrow> bool"
  (SML "IntInf.< ((_), (_))")
  (OCaml "Big'_int.lt'_big'_int")
  (Haskell infix 4 "<")
  (Scala infixl 4 "<")
  (Eval infixl 6 "<")

code_modulename SML
  Code_Numeral_Types Arith

code_modulename OCaml
  Code_Numeral_Types Arith

code_modulename Haskell
  Code_Numeral_Types Arith


subsection {* Type of target language naturals *}

typedef natural = "UNIV \<Colon> nat set"
  morphisms nat_of_natural natural_of_nat ..

lemma natural_eq_iff [termination_simp]:
  "m = n \<longleftrightarrow> nat_of_natural m = nat_of_natural n"
  using nat_of_natural_inject [of m n] ..

lemma natural_eqI:
  "nat_of_natural m = nat_of_natural n \<Longrightarrow> m = n"
  using natural_eq_iff [of m n] by simp

lemma nat_of_natural_of_nat_inverse [simp]:
  "nat_of_natural (natural_of_nat n) = n"
  using natural_of_nat_inverse [of n] by simp

lemma natural_of_nat_of_natural_inverse [simp]:
  "natural_of_nat (nat_of_natural n) = n"
  using nat_of_natural_inverse [of n] by simp

instantiation natural :: "{comm_monoid_diff, semiring_1}"
begin

definition
  "0 = natural_of_nat 0"

lemma nat_of_natural_zero [simp]:
  "nat_of_natural 0 = 0"
  by (simp add: zero_natural_def)

definition
  "1 = natural_of_nat 1"

lemma nat_of_natural_one [simp]:
  "nat_of_natural 1 = 1"
  by (simp add: one_natural_def)

definition
  "m + n = natural_of_nat (nat_of_natural m + nat_of_natural n)"

lemma nat_of_natural_plus [simp]:
  "nat_of_natural (m + n) = nat_of_natural m + nat_of_natural n"
  by (simp add: plus_natural_def)

definition
  "m - n = natural_of_nat (nat_of_natural m - nat_of_natural n)"

lemma nat_of_natural_minus [simp]:
  "nat_of_natural (m - n) = nat_of_natural m - nat_of_natural n"
  by (simp add: minus_natural_def)

definition
  "m * n = natural_of_nat (nat_of_natural m * nat_of_natural n)"

lemma nat_of_natural_times [simp]:
  "nat_of_natural (m * n) = nat_of_natural m * nat_of_natural n"
  by (simp add: times_natural_def)

instance proof
qed (auto simp add: natural_eq_iff algebra_simps)

end

lemma nat_of_natural_of_nat [simp]:
  "nat_of_natural (of_nat n) = n"
  by (induct n) simp_all

lemma natural_of_nat_of_nat [simp, code_abbrev]:
  "natural_of_nat = of_nat"
  by rule (simp add: natural_eq_iff)

lemma of_nat_of_natural [simp]:
  "of_nat (nat_of_natural n) = n"
  using natural_of_nat_of_natural_inverse [of n] by simp

lemma nat_of_natural_numeral [simp]:
  "nat_of_natural (numeral k) = numeral k"
  using nat_of_natural_of_nat [of "numeral k"] by simp

instantiation natural :: "{semiring_div, equal, linordered_semiring}"
begin

definition
  "m div n = natural_of_nat (nat_of_natural m div nat_of_natural n)"

lemma nat_of_natural_div [simp]:
  "nat_of_natural (m div n) = nat_of_natural m div nat_of_natural n"
  by (simp add: div_natural_def)

definition
  "m mod n = natural_of_nat (nat_of_natural m mod nat_of_natural n)"

lemma nat_of_natural_mod [simp]:
  "nat_of_natural (m mod n) = nat_of_natural m mod nat_of_natural n"
  by (simp add: mod_natural_def)

definition
  [termination_simp]: "m \<le> n \<longleftrightarrow> nat_of_natural m \<le> nat_of_natural n"

definition
  [termination_simp]: "m < n \<longleftrightarrow> nat_of_natural m < nat_of_natural n"

definition
  "HOL.equal m n \<longleftrightarrow> HOL.equal (nat_of_natural m) (nat_of_natural n)"

instance proof
qed (auto simp add: natural_eq_iff algebra_simps
  less_eq_natural_def less_natural_def equal_natural_def equal)

end

lemma nat_of_natural_min [simp]:
  "nat_of_natural (min k l) = min (nat_of_natural k) (nat_of_natural l)"
  by (simp add: min_def less_eq_natural_def)

lemma nat_of_natural_max [simp]:
  "nat_of_natural (max k l) = max (nat_of_natural k) (nat_of_natural l)"
  by (simp add: max_def less_eq_natural_def)

definition natural_of_integer :: "integer \<Rightarrow> natural"
where
  "natural_of_integer = of_nat \<circ> nat_of_integer"

definition integer_of_natural :: "natural \<Rightarrow> integer"
where
  "integer_of_natural = of_nat \<circ> nat_of_natural"

lemma natural_of_integer_of_natural [simp]:
  "natural_of_integer (integer_of_natural n) = n"
  by (simp add: natural_of_integer_def integer_of_natural_def natural_eq_iff)

lemma integer_of_natural_of_integer [simp]:
  "integer_of_natural (natural_of_integer k) = max 0 k"
  by (simp add: natural_of_integer_def integer_of_natural_def integer_eq_iff)

lemma int_of_integer_of_natural [simp]:
  "int_of_integer (integer_of_natural n) = of_nat (nat_of_natural n)"
  by (simp add: integer_of_natural_def)

lemma integer_of_natural_of_nat [simp]:
  "integer_of_natural (of_nat n) = of_nat n"
  by (simp add: integer_eq_iff)

lemma [measure_function]:
  "is_measure nat_of_natural" by (rule is_measure_trivial)


subsection {* Inductive represenation of target language naturals *}

definition Suc :: "natural \<Rightarrow> natural"
where
  "Suc = natural_of_nat \<circ> Nat.Suc \<circ> nat_of_natural"

lemma nat_of_natural_Suc [simp]:
  "nat_of_natural (Suc n) = Nat.Suc (nat_of_natural n)"
  by (simp add: Suc_def)

rep_datatype "0::natural" Suc
proof -
  fix P :: "natural \<Rightarrow> bool"
  fix n :: natural
  assume "P 0" then have init: "P (natural_of_nat 0)" by simp
  assume "\<And>n. P n \<Longrightarrow> P (Suc n)"
    then have "\<And>n. P (natural_of_nat n) \<Longrightarrow> P (Suc (natural_of_nat n))" .
    then have step: "\<And>n. P (natural_of_nat n) \<Longrightarrow> P (natural_of_nat (Nat.Suc n))"
      by (simp add: Suc_def)
  from init step have "P (natural_of_nat (nat_of_natural n))"
    by (rule nat.induct)
  with natural_of_nat_of_natural_inverse show "P n" by simp
qed (simp_all add: natural_eq_iff)

lemma natural_case [case_names nat, cases type: natural]:
  fixes m :: natural
  assumes "\<And>n. m = of_nat n \<Longrightarrow> P"
  shows P
  by (rule assms [of "nat_of_natural m"]) simp

lemma [simp, code]:
  "natural_size = nat_of_natural"
proof (rule ext)
  fix n
  show "natural_size n = nat_of_natural n"
    by (induct n) simp_all
qed

lemma [simp, code]:
  "size = nat_of_natural"
proof (rule ext)
  fix n
  show "size n = nat_of_natural n"
    by (induct n) simp_all
qed

lemma natural_decr [termination_simp]:
  "n \<noteq> 0 \<Longrightarrow> nat_of_natural n - Nat.Suc 0 < nat_of_natural n"
  by (simp add: natural_eq_iff)

lemma natural_zero_minus_one:
  "(0::natural) - 1 = 0"
  by simp

lemma Suc_natural_minus_one:
  "Suc n - 1 = n"
  by (simp add: natural_eq_iff)

hide_const (open) Suc


subsection {* Code refinement for target language naturals *}

definition Nat :: "integer \<Rightarrow> natural"
where
  "Nat = natural_of_integer"

lemma [code abstype]:
  "Nat (integer_of_natural n) = n"
  by (unfold Nat_def) (fact natural_of_integer_of_natural)

lemma [code abstract]:
  "integer_of_natural (natural_of_nat n) = of_nat n"
  by simp

lemma [code abstract]:
  "integer_of_natural (natural_of_integer k) = max 0 k"
  by simp

lemma [code_abbrev]:
  "natural_of_integer (Code_Numeral_Types.Pos k) = numeral k"
  by (simp add: nat_of_integer_def natural_of_integer_def)

lemma [code abstract]:
  "integer_of_natural 0 = 0"
  by (simp add: integer_eq_iff)

lemma [code abstract]:
  "integer_of_natural 1 = 1"
  by (simp add: integer_eq_iff)

lemma [code abstract]:
  "integer_of_natural (Code_Numeral_Types.Suc n) = integer_of_natural n + 1"
  by (simp add: integer_eq_iff)

lemma [code]:
  "nat_of_natural = nat_of_integer \<circ> integer_of_natural"
  by (simp add: integer_of_natural_def fun_eq_iff)

lemma [code, code_unfold]:
  "natural_case f g n = (if n = 0 then f else g (n - 1))"
  by (cases n rule: natural.exhaust) (simp_all, simp add: Suc_def)

declare natural.recs [code del]

lemma [code abstract]:
  "integer_of_natural (m + n) = integer_of_natural m + integer_of_natural n"
  by (simp add: integer_eq_iff)

lemma [code abstract]:
  "integer_of_natural (m - n) = max 0 (integer_of_natural m - integer_of_natural n)"
  by (simp add: integer_eq_iff)

lemma [code abstract]:
  "integer_of_natural (m * n) = integer_of_natural m * integer_of_natural n"
  by (simp add: integer_eq_iff of_nat_mult)

lemma [code abstract]:
  "integer_of_natural (m div n) = integer_of_natural m div integer_of_natural n"
  by (simp add: integer_eq_iff zdiv_int)

lemma [code abstract]:
  "integer_of_natural (m mod n) = integer_of_natural m mod integer_of_natural n"
  by (simp add: integer_eq_iff zmod_int)

lemma [code]:
  "HOL.equal m n \<longleftrightarrow> HOL.equal (integer_of_natural m) (integer_of_natural n)"
  by (simp add: equal natural_eq_iff integer_eq_iff)

lemma [code nbe]:
  "HOL.equal n (n::natural) \<longleftrightarrow> True"
  by (simp add: equal)

lemma [code]:
  "m \<le> n \<longleftrightarrow> (integer_of_natural m) \<le> integer_of_natural n"
  by (simp add: less_eq_natural_def less_eq_integer_def)

lemma [code]:
  "m < n \<longleftrightarrow> (integer_of_natural m) < integer_of_natural n"
  by (simp add: less_natural_def less_integer_def)

hide_const (open) Nat


code_reflect Code_Numeral_Types
  datatypes natural = _
  functions integer_of_natural natural_of_integer

end

