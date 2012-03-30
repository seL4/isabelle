theory Target_Numeral
imports Main Code_Nat
begin

subsection {* Type of target language numerals *}

typedef (open) int = "UNIV \<Colon> int set"
  morphisms int_of of_int ..

hide_type (open) int
hide_const (open) of_int

lemma int_eq_iff:
  "k = l \<longleftrightarrow> int_of k = int_of l"
  using int_of_inject [of k l] ..

lemma int_eqI:
  "int_of k = int_of l \<Longrightarrow> k = l"
  using int_eq_iff [of k l] by simp

lemma int_of_int [simp]:
  "int_of (Target_Numeral.of_int k) = k"
  using of_int_inverse [of k] by simp

lemma of_int_of [simp]:
  "Target_Numeral.of_int (int_of k) = k"
  using int_of_inverse [of k] by simp

hide_fact (open) int_eq_iff int_eqI

instantiation Target_Numeral.int :: ring_1
begin

definition
  "0 = Target_Numeral.of_int 0"

lemma int_of_zero [simp]:
  "int_of 0 = 0"
  by (simp add: zero_int_def)

definition
  "1 = Target_Numeral.of_int 1"

lemma int_of_one [simp]:
  "int_of 1 = 1"
  by (simp add: one_int_def)

definition
  "k + l = Target_Numeral.of_int (int_of k + int_of l)"

lemma int_of_plus [simp]:
  "int_of (k + l) = int_of k + int_of l"
  by (simp add: plus_int_def)

definition
  "- k = Target_Numeral.of_int (- int_of k)"

lemma int_of_uminus [simp]:
  "int_of (- k) = - int_of k"
  by (simp add: uminus_int_def)

definition
  "k - l = Target_Numeral.of_int (int_of k - int_of l)"

lemma int_of_minus [simp]:
  "int_of (k - l) = int_of k - int_of l"
  by (simp add: minus_int_def)

definition
  "k * l = Target_Numeral.of_int (int_of k * int_of l)"

lemma int_of_times [simp]:
  "int_of (k * l) = int_of k * int_of l"
  by (simp add: times_int_def)

instance proof
qed (auto simp add: Target_Numeral.int_eq_iff algebra_simps)

end

lemma int_of_of_nat [simp]:
  "int_of (of_nat n) = of_nat n"
  by (induct n) simp_all

definition nat_of :: "Target_Numeral.int \<Rightarrow> nat" where
  "nat_of k = Int.nat (int_of k)"

lemma nat_of_of_nat [simp]:
  "nat_of (of_nat n) = n"
  by (simp add: nat_of_def)

lemma int_of_of_int [simp]:
  "int_of (of_int k) = k"
  by (induct k) (simp_all, simp only: neg_numeral_def numeral_One int_of_uminus int_of_one)

lemma of_int_of_int [simp, code_abbrev]:
  "Target_Numeral.of_int = of_int"
  by rule (simp add: Target_Numeral.int_eq_iff)

lemma int_of_numeral [simp]:
  "int_of (numeral k) = numeral k"
  using int_of_of_int [of "numeral k"] by simp

lemma int_of_neg_numeral [simp]:
  "int_of (neg_numeral k) = neg_numeral k"
  by (simp only: neg_numeral_def int_of_uminus) simp

lemma int_of_sub [simp]:
  "int_of (Num.sub k l) = Num.sub k l"
  by (simp only: Num.sub_def int_of_minus int_of_numeral)

instantiation Target_Numeral.int :: "{ring_div, equal, linordered_idom}"
begin

definition
  "k div l = of_int (int_of k div int_of l)"

lemma int_of_div [simp]:
  "int_of (k div l) = int_of k div int_of l"
  by (simp add: div_int_def)

definition
  "k mod l = of_int (int_of k mod int_of l)"

lemma int_of_mod [simp]:
  "int_of (k mod l) = int_of k mod int_of l"
  by (simp add: mod_int_def)

definition
  "\<bar>k\<bar> = of_int \<bar>int_of k\<bar>"

lemma int_of_abs [simp]:
  "int_of \<bar>k\<bar> = \<bar>int_of k\<bar>"
  by (simp add: abs_int_def)

definition
  "sgn k = of_int (sgn (int_of k))"

lemma int_of_sgn [simp]:
  "int_of (sgn k) = sgn (int_of k)"
  by (simp add: sgn_int_def)

definition
  "k \<le> l \<longleftrightarrow> int_of k \<le> int_of l"

definition
  "k < l \<longleftrightarrow> int_of k < int_of l"

definition
  "HOL.equal k l \<longleftrightarrow> HOL.equal (int_of k) (int_of l)"

instance proof
qed (auto simp add: Target_Numeral.int_eq_iff algebra_simps
  less_eq_int_def less_int_def equal_int_def equal)

end

lemma int_of_min [simp]:
  "int_of (min k l) = min (int_of k) (int_of l)"
  by (simp add: min_def less_eq_int_def)

lemma int_of_max [simp]:
  "int_of (max k l) = max (int_of k) (int_of l)"
  by (simp add: max_def less_eq_int_def)


subsection {* Code theorems for target language numerals *}

text {* Constructors *}

definition Pos :: "num \<Rightarrow> Target_Numeral.int" where
  [simp, code_abbrev]: "Pos = numeral"

definition Neg :: "num \<Rightarrow> Target_Numeral.int" where
  [simp, code_abbrev]: "Neg = neg_numeral"

code_datatype "0::Target_Numeral.int" Pos Neg


text {* Auxiliary operations *}

definition dup :: "Target_Numeral.int \<Rightarrow> Target_Numeral.int" where
  [simp]: "dup k = k + k"

lemma dup_code [code]:
  "dup 0 = 0"
  "dup (Pos n) = Pos (Num.Bit0 n)"
  "dup (Neg n) = Neg (Num.Bit0 n)"
  unfolding Pos_def Neg_def neg_numeral_def
  by (simp_all add: numeral_Bit0)

definition sub :: "num \<Rightarrow> num \<Rightarrow> Target_Numeral.int" where
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

lemma one_int_code [code, code_unfold]:
  "1 = Pos Num.One"
  by simp

lemma plus_int_code [code]:
  "k + 0 = (k::Target_Numeral.int)"
  "0 + l = (l::Target_Numeral.int)"
  "Pos m + Pos n = Pos (m + n)"
  "Pos m + Neg n = sub m n"
  "Neg m + Pos n = sub n m"
  "Neg m + Neg n = Neg (m + n)"
  by simp_all

lemma uminus_int_code [code]:
  "uminus 0 = (0::Target_Numeral.int)"
  "uminus (Pos m) = Neg m"
  "uminus (Neg m) = Pos m"
  by simp_all

lemma minus_int_code [code]:
  "k - 0 = (k::Target_Numeral.int)"
  "0 - l = uminus (l::Target_Numeral.int)"
  "Pos m - Pos n = sub m n"
  "Pos m - Neg n = Pos (m + n)"
  "Neg m - Pos n = Neg (m + n)"
  "Neg m - Neg n = sub n m"
  by simp_all

lemma times_int_code [code]:
  "k * 0 = (0::Target_Numeral.int)"
  "0 * l = (0::Target_Numeral.int)"
  "Pos m * Pos n = Pos (m * n)"
  "Pos m * Neg n = Neg (m * n)"
  "Neg m * Pos n = Neg (m * n)"
  "Neg m * Neg n = Pos (m * n)"
  by simp_all

definition divmod :: "Target_Numeral.int \<Rightarrow> Target_Numeral.int \<Rightarrow> Target_Numeral.int \<times> Target_Numeral.int" where
  "divmod k l = (k div l, k mod l)"

lemma fst_divmod [simp]:
  "fst (divmod k l) = k div l"
  by (simp add: divmod_def)

lemma snd_divmod [simp]:
  "snd (divmod k l) = k mod l"
  by (simp add: divmod_def)

definition divmod_abs :: "Target_Numeral.int \<Rightarrow> Target_Numeral.int \<Rightarrow> Target_Numeral.int \<times> Target_Numeral.int" where
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
  by (auto simp add: prod_eq_iff Target_Numeral.int_eq_iff Let_def prod_case_beta
    sub_non_negative sub_negative div_pos_pos_trivial mod_pos_pos_trivial div_pos_geq mod_pos_geq)

lemma divmod_code [code]: "divmod k l =
  (if k = 0 then (0, 0) else if l = 0 then (0, k) else
  (apsnd \<circ> times \<circ> sgn) l (if sgn k = sgn l
    then divmod_abs k l
    else (let (r, s) = divmod_abs k l in
      if s = 0 then (- r, 0) else (- r - 1, \<bar>l\<bar> - s))))"
proof -
  have aux1: "\<And>k l::int. sgn k = sgn l \<longleftrightarrow> k = 0 \<and> l = 0 \<or> 0 < l \<and> 0 < k \<or> l < 0 \<and> k < 0"
    by (auto simp add: sgn_if)
  have aux2: "\<And>q::int. - int_of k = int_of l * q \<longleftrightarrow> int_of k = int_of l * - q" by auto
  show ?thesis
    by (simp add: prod_eq_iff Target_Numeral.int_eq_iff prod_case_beta aux1)
      (auto simp add: zdiv_zminus1_eq_if zmod_zminus1_eq_if div_minus_right mod_minus_right aux2)
qed

lemma div_int_code [code]:
  "k div l = fst (divmod k l)"
  by simp

lemma div_mod_code [code]:
  "k mod l = snd (divmod k l)"
  by simp

lemma equal_int_code [code]:
  "HOL.equal 0 (0::Target_Numeral.int) \<longleftrightarrow> True"
  "HOL.equal 0 (Pos l) \<longleftrightarrow> False"
  "HOL.equal 0 (Neg l) \<longleftrightarrow> False"
  "HOL.equal (Pos k) 0 \<longleftrightarrow> False"
  "HOL.equal (Pos k) (Pos l) \<longleftrightarrow> HOL.equal k l"
  "HOL.equal (Pos k) (Neg l) \<longleftrightarrow> False"
  "HOL.equal (Neg k) 0 \<longleftrightarrow> False"
  "HOL.equal (Neg k) (Pos l) \<longleftrightarrow> False"
  "HOL.equal (Neg k) (Neg l) \<longleftrightarrow> HOL.equal k l"
  by (simp_all add: equal Target_Numeral.int_eq_iff)

lemma equal_int_refl [code nbe]:
  "HOL.equal (k::Target_Numeral.int) k \<longleftrightarrow> True"
  by (fact equal_refl)

lemma less_eq_int_code [code]:
  "0 \<le> (0::Target_Numeral.int) \<longleftrightarrow> True"
  "0 \<le> Pos l \<longleftrightarrow> True"
  "0 \<le> Neg l \<longleftrightarrow> False"
  "Pos k \<le> 0 \<longleftrightarrow> False"
  "Pos k \<le> Pos l \<longleftrightarrow> k \<le> l"
  "Pos k \<le> Neg l \<longleftrightarrow> False"
  "Neg k \<le> 0 \<longleftrightarrow> True"
  "Neg k \<le> Pos l \<longleftrightarrow> True"
  "Neg k \<le> Neg l \<longleftrightarrow> l \<le> k"
  by (simp_all add: less_eq_int_def)

lemma less_int_code [code]:
  "0 < (0::Target_Numeral.int) \<longleftrightarrow> False"
  "0 < Pos l \<longleftrightarrow> True"
  "0 < Neg l \<longleftrightarrow> False"
  "Pos k < 0 \<longleftrightarrow> False"
  "Pos k < Pos l \<longleftrightarrow> k < l"
  "Pos k < Neg l \<longleftrightarrow> False"
  "Neg k < 0 \<longleftrightarrow> True"
  "Neg k < Pos l \<longleftrightarrow> True"
  "Neg k < Neg l \<longleftrightarrow> l < k"
  by (simp_all add: less_int_def)

lemma nat_of_code [code]:
  "nat_of (Neg k) = 0"
  "nat_of 0 = 0"
  "nat_of (Pos k) = nat_of_num k"
  by (simp_all add: nat_of_def nat_of_num_numeral)

lemma int_of_code [code]:
  "int_of (Neg k) = neg_numeral k"
  "int_of 0 = 0"
  "int_of (Pos k) = numeral k"
  by simp_all

lemma of_int_code [code]:
  "Target_Numeral.of_int (Int.Neg k) = neg_numeral k"
  "Target_Numeral.of_int 0 = 0"
  "Target_Numeral.of_int (Int.Pos k) = numeral k"
  by simp_all

definition num_of_int :: "Target_Numeral.int \<Rightarrow> num" where
  "num_of_int = num_of_nat \<circ> nat_of"

lemma num_of_int_code [code]:
  "num_of_int k = (if k \<le> 1 then Num.One
     else let
       (l, j) = divmod k 2;
       l' = num_of_int l + num_of_int l
     in if j = 0 then l' else l' + Num.One)"
proof -
  {
    assume "int_of k mod 2 = 1"
    then have "nat (int_of k mod 2) = nat 1" by simp
    moreover assume *: "1 < int_of k"
    ultimately have **: "nat (int_of k) mod 2 = 1" by (simp add: nat_mod_distrib)
    have "num_of_nat (nat (int_of k)) =
      num_of_nat (2 * (nat (int_of k) div 2) + nat (int_of k) mod 2)"
      by simp
    then have "num_of_nat (nat (int_of k)) =
      num_of_nat (nat (int_of k) div 2 + nat (int_of k) div 2 + nat (int_of k) mod 2)"
      by (simp add: mult_2)
    with ** have "num_of_nat (nat (int_of k)) =
      num_of_nat (nat (int_of k) div 2 + nat (int_of k) div 2 + 1)"
      by simp
  }
  note aux = this
  show ?thesis
    by (auto simp add: num_of_int_def nat_of_def Let_def prod_case_beta
      not_le Target_Numeral.int_eq_iff less_eq_int_def
      nat_mult_distrib nat_div_distrib num_of_nat_One num_of_nat_plus_distrib
       mult_2 [where 'a=nat] aux add_One)
qed

hide_const (open) int_of nat_of Pos Neg sub dup divmod_abs num_of_int


subsection {* Serializer setup for target language numerals *}

code_type Target_Numeral.int
  (SML "IntInf.int")
  (OCaml "Big'_int.big'_int")
  (Haskell "Integer")
  (Scala "BigInt")
  (Eval "int")

code_instance Target_Numeral.int :: equal
  (Haskell -)

code_const "0::Target_Numeral.int"
  (SML "0")
  (OCaml "Big'_int.zero'_big'_int")
  (Haskell "0")
  (Scala "BigInt(0)")

setup {*
  fold (Numeral.add_code @{const_name Target_Numeral.Pos}
    false Code_Printer.literal_numeral) ["SML", "OCaml", "Haskell", "Scala"]
*}

setup {*
  fold (Numeral.add_code @{const_name Target_Numeral.Neg}
    true Code_Printer.literal_numeral) ["SML", "OCaml", "Haskell", "Scala"]
*}

code_const "plus :: Target_Numeral.int \<Rightarrow> _ \<Rightarrow> _"
  (SML "IntInf.+ ((_), (_))")
  (OCaml "Big'_int.add'_big'_int")
  (Haskell infixl 6 "+")
  (Scala infixl 7 "+")
  (Eval infixl 8 "+")

code_const "uminus :: Target_Numeral.int \<Rightarrow> _"
  (SML "IntInf.~")
  (OCaml "Big'_int.minus'_big'_int")
  (Haskell "negate")
  (Scala "!(- _)")
  (Eval "~/ _")

code_const "minus :: Target_Numeral.int \<Rightarrow> _"
  (SML "IntInf.- ((_), (_))")
  (OCaml "Big'_int.sub'_big'_int")
  (Haskell infixl 6 "-")
  (Scala infixl 7 "-")
  (Eval infixl 8 "-")

code_const Target_Numeral.dup
  (SML "IntInf.*/ (2,/ (_))")
  (OCaml "Big'_int.mult'_big'_int/ 2")
  (Haskell "!(2 * _)")
  (Scala "!(2 * _)")
  (Eval "!(2 * _)")

code_const Target_Numeral.sub
  (SML "!(raise/ Fail/ \"sub\")")
  (OCaml "failwith/ \"sub\"")
  (Haskell "error/ \"sub\"")
  (Scala "!error(\"sub\")")

code_const "times :: Target_Numeral.int \<Rightarrow> _ \<Rightarrow> _"
  (SML "IntInf.* ((_), (_))")
  (OCaml "Big'_int.mult'_big'_int")
  (Haskell infixl 7 "*")
  (Scala infixl 8 "*")
  (Eval infixl 9 "*")

code_const Target_Numeral.divmod_abs
  (SML "IntInf.divMod/ (IntInf.abs _,/ IntInf.abs _)")
  (OCaml "Big'_int.quomod'_big'_int/ (Big'_int.abs'_big'_int _)/ (Big'_int.abs'_big'_int _)")
  (Haskell "divMod/ (abs _)/ (abs _)")
  (Scala "!((k: BigInt) => (l: BigInt) =>/ if (l == 0)/ (BigInt(0), k) else/ (k.abs '/% l.abs))")
  (Eval "Integer.div'_mod/ (abs _)/ (abs _)")

code_const "HOL.equal :: Target_Numeral.int \<Rightarrow> _ \<Rightarrow> bool"
  (SML "!((_ : IntInf.int) = _)")
  (OCaml "Big'_int.eq'_big'_int")
  (Haskell infix 4 "==")
  (Scala infixl 5 "==")
  (Eval infixl 6 "=")

code_const "less_eq :: Target_Numeral.int \<Rightarrow> _ \<Rightarrow> bool"
  (SML "IntInf.<= ((_), (_))")
  (OCaml "Big'_int.le'_big'_int")
  (Haskell infix 4 "<=")
  (Scala infixl 4 "<=")
  (Eval infixl 6 "<=")

code_const "less :: Target_Numeral.int \<Rightarrow> _ \<Rightarrow> bool"
  (SML "IntInf.< ((_), (_))")
  (OCaml "Big'_int.lt'_big'_int")
  (Haskell infix 4 "<")
  (Scala infixl 4 "<")
  (Eval infixl 6 "<")

ML {*
structure Target_Numeral =
struct

val T = @{typ "Target_Numeral.int"};

end;
*}

code_reserved Eval Target_Numeral

code_const "Code_Evaluation.term_of \<Colon> Target_Numeral.int \<Rightarrow> term"
  (Eval "HOLogic.mk'_number/ Target'_Numeral.T")

code_modulename SML
  Target_Numeral Arith

code_modulename OCaml
  Target_Numeral Arith

code_modulename Haskell
  Target_Numeral Arith


subsection {* Implementation for @{typ int} *}

code_datatype Target_Numeral.int_of

lemma [code, code del]:
  "Target_Numeral.of_int = Target_Numeral.of_int" ..

lemma [code]:
  "Target_Numeral.of_int (Target_Numeral.int_of k) = k"
  by (simp add: Target_Numeral.int_eq_iff)

declare Int.Pos_def [code]

lemma [code_abbrev]:
  "Target_Numeral.int_of (Target_Numeral.Pos k) = Int.Pos k"
  by simp

declare Int.Neg_def [code]

lemma [code_abbrev]:
  "Target_Numeral.int_of (Target_Numeral.Neg k) = Int.Neg k"
  by simp

lemma [code]:
  "0 = Target_Numeral.int_of 0"
  by simp

lemma [code]:
  "1 = Target_Numeral.int_of 1"
  by simp

lemma [code]:
  "k + l = Target_Numeral.int_of (of_int k + of_int l)"
  by simp

lemma [code]:
  "- k = Target_Numeral.int_of (- of_int k)"
  by simp

lemma [code]:
  "k - l = Target_Numeral.int_of (of_int k - of_int l)"
  by simp

lemma [code]:
  "Int.dup k = Target_Numeral.int_of (Target_Numeral.dup (of_int k))"
  by simp

lemma [code, code del]:
  "Int.sub = Int.sub" ..

lemma [code]:
  "k * l = Target_Numeral.int_of (of_int k * of_int l)"
  by simp

lemma [code]:
  "pdivmod k l = map_pair Target_Numeral.int_of Target_Numeral.int_of
    (Target_Numeral.divmod_abs (of_int k) (of_int l))"
  by (simp add: prod_eq_iff pdivmod_def)

lemma [code]:
  "k div l = Target_Numeral.int_of (of_int k div of_int l)"
  by simp

lemma [code]:
  "k mod l = Target_Numeral.int_of (of_int k mod of_int l)"
  by simp

lemma [code]:
  "HOL.equal k l = HOL.equal (of_int k :: Target_Numeral.int) (of_int l)"
  by (simp add: equal Target_Numeral.int_eq_iff)

lemma [code]:
  "k \<le> l \<longleftrightarrow> (of_int k :: Target_Numeral.int) \<le> of_int l"
  by (simp add: less_eq_int_def)

lemma [code]:
  "k < l \<longleftrightarrow> (of_int k :: Target_Numeral.int) < of_int l"
  by (simp add: less_int_def)

lemma (in ring_1) of_int_code:
  "of_int k = (if k = 0 then 0
     else if k < 0 then - of_int (- k)
     else let
       (l, j) = divmod_int k 2;
       l' = 2 * of_int l
     in if j = 0 then l' else l' + 1)"
proof -
  from mod_div_equality have *: "of_int k = of_int (k div 2 * 2 + k mod 2)" by simp
  show ?thesis
    by (simp add: Let_def divmod_int_mod_div mod_2_not_eq_zero_eq_one_int
      of_int_add [symmetric]) (simp add: * mult_commute)
qed

declare of_int_code [code]


subsection {* Implementation for @{typ nat} *}

definition of_nat :: "nat \<Rightarrow> Target_Numeral.int" where
  [code_abbrev]: "of_nat = Nat.of_nat"

hide_const (open) of_nat

lemma int_of_nat [simp]:
  "Target_Numeral.int_of (Target_Numeral.of_nat n) = of_nat n"
  by (simp add: of_nat_def)

lemma [code abstype]:
  "Target_Numeral.nat_of (Target_Numeral.of_nat n) = n"
  by (simp add: nat_of_def)

lemma [code_abbrev]:
  "nat (Int.Pos k) = nat_of_num k"
  by (simp add: nat_of_num_numeral)

lemma [code abstract]:
  "Target_Numeral.of_nat 0 = 0"
  by (simp add: Target_Numeral.int_eq_iff)

lemma [code abstract]:
  "Target_Numeral.of_nat 1 = 1"
  by (simp add: Target_Numeral.int_eq_iff)

lemma [code abstract]:
  "Target_Numeral.of_nat (m + n) = of_nat m + of_nat n"
  by (simp add: Target_Numeral.int_eq_iff)

lemma [code abstract]:
  "Target_Numeral.of_nat (Code_Nat.dup n) = Target_Numeral.dup (of_nat n)"
  by (simp add: Target_Numeral.int_eq_iff Code_Nat.dup_def)

lemma [code, code del]:
  "Code_Nat.sub = Code_Nat.sub" ..

lemma [code abstract]:
  "Target_Numeral.of_nat (m - n) = max 0 (of_nat m - of_nat n)"
  by (simp add: Target_Numeral.int_eq_iff)

lemma [code abstract]:
  "Target_Numeral.of_nat (m * n) = of_nat m * of_nat n"
  by (simp add: Target_Numeral.int_eq_iff of_nat_mult)

lemma [code abstract]:
  "Target_Numeral.of_nat (m div n) = of_nat m div of_nat n"
  by (simp add: Target_Numeral.int_eq_iff zdiv_int)

lemma [code abstract]:
  "Target_Numeral.of_nat (m mod n) = of_nat m mod of_nat n"
  by (simp add: Target_Numeral.int_eq_iff zmod_int)

lemma [code]:
  "Divides.divmod_nat m n = (m div n, m mod n)"
  by (simp add: prod_eq_iff)

lemma [code]:
  "HOL.equal m n = HOL.equal (of_nat m :: Target_Numeral.int) (of_nat n)"
  by (simp add: equal Target_Numeral.int_eq_iff)

lemma [code]:
  "m \<le> n \<longleftrightarrow> (of_nat m :: Target_Numeral.int) \<le> of_nat n"
  by (simp add: less_eq_int_def)

lemma [code]:
  "m < n \<longleftrightarrow> (of_nat m :: Target_Numeral.int) < of_nat n"
  by (simp add: less_int_def)

lemma num_of_nat_code [code]:
  "num_of_nat = Target_Numeral.num_of_int \<circ> Target_Numeral.of_nat"
  by (simp add: fun_eq_iff num_of_int_def of_nat_def)

lemma (in semiring_1) of_nat_code:
  "of_nat n = (if n = 0 then 0
     else let
       (m, q) = divmod_nat n 2;
       m' = 2 * of_nat m
     in if q = 0 then m' else m' + 1)"
proof -
  from mod_div_equality have *: "of_nat n = of_nat (n div 2 * 2 + n mod 2)" by simp
  show ?thesis
    by (simp add: Let_def divmod_nat_div_mod mod_2_not_eq_zero_eq_one_nat
      of_nat_add [symmetric])
      (simp add: * mult_commute of_nat_mult add_commute)
qed

declare of_nat_code [code]

text {* Conversions between @{typ nat} and @{typ int} *}

definition int :: "nat \<Rightarrow> int" where
  [code_abbrev]: "int = of_nat"

hide_const (open) int

lemma [code]:
  "Target_Numeral.int n = Target_Numeral.int_of (of_nat n)"
  by (simp add: int_def)

lemma [code abstract]:
  "Target_Numeral.of_nat (nat k) = max 0 (Target_Numeral.of_int k)"
  by (simp add: of_nat_def of_int_of_nat max_def)

end
