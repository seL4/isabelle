(*  Title:      HOL/Int.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Tobias Nipkow, Florian Haftmann, TU Muenchen
*)

header {* The Integers as Equivalence Classes over Pairs of Natural Numbers *} 

theory Int
imports Equiv_Relations Wellfounded Quotient
begin

subsection {* Definition of integers as a quotient type *}

definition intrel :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool" where
  "intrel = (\<lambda>(x, y) (u, v). x + v = u + y)"

lemma intrel_iff [simp]: "intrel (x, y) (u, v) \<longleftrightarrow> x + v = u + y"
  by (simp add: intrel_def)

quotient_type int = "nat \<times> nat" / "intrel"
  morphisms Rep_Integ Abs_Integ
proof (rule equivpI)
  show "reflp intrel"
    unfolding reflp_def by auto
  show "symp intrel"
    unfolding symp_def by auto
  show "transp intrel"
    unfolding transp_def by auto
qed

lemma eq_Abs_Integ [case_names Abs_Integ, cases type: int]:
     "(!!x y. z = Abs_Integ (x, y) ==> P) ==> P"
by (induct z) auto

subsection {* Integers form a commutative ring *}

instantiation int :: comm_ring_1
begin

lift_definition zero_int :: "int" is "(0, 0)"
  by simp

lift_definition one_int :: "int" is "(1, 0)"
  by simp

lift_definition plus_int :: "int \<Rightarrow> int \<Rightarrow> int"
  is "\<lambda>(x, y) (u, v). (x + u, y + v)"
  by clarsimp

lift_definition uminus_int :: "int \<Rightarrow> int"
  is "\<lambda>(x, y). (y, x)"
  by clarsimp

lift_definition minus_int :: "int \<Rightarrow> int \<Rightarrow> int"
  is "\<lambda>(x, y) (u, v). (x + v, y + u)"
  by clarsimp

lift_definition times_int :: "int \<Rightarrow> int \<Rightarrow> int"
  is "\<lambda>(x, y) (u, v). (x*u + y*v, x*v + y*u)"
proof (clarsimp)
  fix s t u v w x y z :: nat
  assume "s + v = u + t" and "w + z = y + x"
  hence "(s + v) * w + (u + t) * x + u * (w + z) + v * (y + x)
       = (u + t) * w + (s + v) * x + u * (y + x) + v * (w + z)"
    by simp
  thus "(s * w + t * x) + (u * z + v * y) = (u * y + v * z) + (s * x + t * w)"
    by (simp add: algebra_simps)
qed

instance
  by default (transfer, clarsimp simp: algebra_simps)+

end

abbreviation int :: "nat \<Rightarrow> int" where
  "int \<equiv> of_nat"

lemma int_def: "int n = Abs_Integ (n, 0)"
  by (induct n, simp add: zero_int.abs_eq,
    simp add: one_int.abs_eq plus_int.abs_eq)

lemma int_transfer [transfer_rule]:
  "(fun_rel (op =) cr_int) (\<lambda>n. (n, 0)) int"
  unfolding fun_rel_def cr_int_def int_def by simp

lemma int_diff_cases:
  obtains (diff) m n where "z = int m - int n"
  by transfer clarsimp

subsection {* Integers are totally ordered *}

instantiation int :: linorder
begin

lift_definition less_eq_int :: "int \<Rightarrow> int \<Rightarrow> bool"
  is "\<lambda>(x, y) (u, v). x + v \<le> u + y"
  by auto

lift_definition less_int :: "int \<Rightarrow> int \<Rightarrow> bool"
  is "\<lambda>(x, y) (u, v). x + v < u + y"
  by auto

instance
  by default (transfer, force)+

end

instantiation int :: distrib_lattice
begin

definition
  "(inf \<Colon> int \<Rightarrow> int \<Rightarrow> int) = min"

definition
  "(sup \<Colon> int \<Rightarrow> int \<Rightarrow> int) = max"

instance
  by intro_classes
    (auto simp add: inf_int_def sup_int_def min_max.sup_inf_distrib1)

end

subsection {* Ordering properties of arithmetic operations *}

instance int :: ordered_cancel_ab_semigroup_add
proof
  fix i j k :: int
  show "i \<le> j \<Longrightarrow> k + i \<le> k + j"
    by transfer clarsimp
qed

text{*Strict Monotonicity of Multiplication*}

text{*strict, in 1st argument; proof is by induction on k>0*}
lemma zmult_zless_mono2_lemma:
     "(i::int)<j ==> 0<k ==> int k * i < int k * j"
apply (induct k)
apply simp
apply (simp add: left_distrib)
apply (case_tac "k=0")
apply (simp_all add: add_strict_mono)
done

lemma zero_le_imp_eq_int: "(0::int) \<le> k ==> \<exists>n. k = int n"
apply transfer
apply clarsimp
apply (rule_tac x="a - b" in exI, simp)
done

lemma zero_less_imp_eq_int: "(0::int) < k ==> \<exists>n>0. k = int n"
apply transfer
apply clarsimp
apply (rule_tac x="a - b" in exI, simp)
done

lemma zmult_zless_mono2: "[| i<j;  (0::int) < k |] ==> k*i < k*j"
apply (drule zero_less_imp_eq_int)
apply (auto simp add: zmult_zless_mono2_lemma)
done

text{*The integers form an ordered integral domain*}
instantiation int :: linordered_idom
begin

definition
  zabs_def: "\<bar>i\<Colon>int\<bar> = (if i < 0 then - i else i)"

definition
  zsgn_def: "sgn (i\<Colon>int) = (if i=0 then 0 else if 0<i then 1 else - 1)"

instance proof
  fix i j k :: int
  show "i < j \<Longrightarrow> 0 < k \<Longrightarrow> k * i < k * j"
    by (rule zmult_zless_mono2)
  show "\<bar>i\<bar> = (if i < 0 then -i else i)"
    by (simp only: zabs_def)
  show "sgn (i\<Colon>int) = (if i=0 then 0 else if 0<i then 1 else - 1)"
    by (simp only: zsgn_def)
qed

end

lemma zless_imp_add1_zle: "w < z \<Longrightarrow> w + (1\<Colon>int) \<le> z"
  by transfer clarsimp

lemma zless_iff_Suc_zadd:
  "(w \<Colon> int) < z \<longleftrightarrow> (\<exists>n. z = w + int (Suc n))"
apply transfer
apply auto
apply (rename_tac a b c d)
apply (rule_tac x="c+b - Suc(a+d)" in exI)
apply arith
done

lemmas int_distrib =
  left_distrib [of z1 z2 w]
  right_distrib [of w z1 z2]
  left_diff_distrib [of z1 z2 w]
  right_diff_distrib [of w z1 z2]
  for z1 z2 w :: int


subsection {* Embedding of the Integers into any @{text ring_1}: @{text of_int}*}

context ring_1
begin

lift_definition of_int :: "int \<Rightarrow> 'a" is "\<lambda>(i, j). of_nat i - of_nat j"
  by (clarsimp simp add: diff_eq_eq eq_diff_eq diff_add_eq
    of_nat_add [symmetric] simp del: of_nat_add)

lemma of_int_0 [simp]: "of_int 0 = 0"
  by transfer simp

lemma of_int_1 [simp]: "of_int 1 = 1"
  by transfer simp

lemma of_int_add [simp]: "of_int (w+z) = of_int w + of_int z"
  by transfer (clarsimp simp add: algebra_simps)

lemma of_int_minus [simp]: "of_int (-z) = - (of_int z)"
  by (transfer fixing: uminus) clarsimp

lemma of_int_diff [simp]: "of_int (w - z) = of_int w - of_int z"
by (simp add: diff_minus Groups.diff_minus)

lemma of_int_mult [simp]: "of_int (w*z) = of_int w * of_int z"
  by (transfer fixing: times) (clarsimp simp add: algebra_simps of_nat_mult)

text{*Collapse nested embeddings*}
lemma of_int_of_nat_eq [simp]: "of_int (int n) = of_nat n"
by (induct n) auto

lemma of_int_numeral [simp, code_post]: "of_int (numeral k) = numeral k"
  by (simp add: of_nat_numeral [symmetric] of_int_of_nat_eq [symmetric])

lemma of_int_neg_numeral [simp, code_post]: "of_int (neg_numeral k) = neg_numeral k"
  unfolding neg_numeral_def neg_numeral_class.neg_numeral_def
  by (simp only: of_int_minus of_int_numeral)

lemma of_int_power:
  "of_int (z ^ n) = of_int z ^ n"
  by (induct n) simp_all

end

context ring_char_0
begin

lemma of_int_eq_iff [simp]:
   "of_int w = of_int z \<longleftrightarrow> w = z"
  by transfer (clarsimp simp add: algebra_simps
    of_nat_add [symmetric] simp del: of_nat_add)

text{*Special cases where either operand is zero*}
lemma of_int_eq_0_iff [simp]:
  "of_int z = 0 \<longleftrightarrow> z = 0"
  using of_int_eq_iff [of z 0] by simp

lemma of_int_0_eq_iff [simp]:
  "0 = of_int z \<longleftrightarrow> z = 0"
  using of_int_eq_iff [of 0 z] by simp

end

context linordered_idom
begin

text{*Every @{text linordered_idom} has characteristic zero.*}
subclass ring_char_0 ..

lemma of_int_le_iff [simp]:
  "of_int w \<le> of_int z \<longleftrightarrow> w \<le> z"
  by (transfer fixing: less_eq) (clarsimp simp add: algebra_simps
    of_nat_add [symmetric] simp del: of_nat_add)

lemma of_int_less_iff [simp]:
  "of_int w < of_int z \<longleftrightarrow> w < z"
  by (simp add: less_le order_less_le)

lemma of_int_0_le_iff [simp]:
  "0 \<le> of_int z \<longleftrightarrow> 0 \<le> z"
  using of_int_le_iff [of 0 z] by simp

lemma of_int_le_0_iff [simp]:
  "of_int z \<le> 0 \<longleftrightarrow> z \<le> 0"
  using of_int_le_iff [of z 0] by simp

lemma of_int_0_less_iff [simp]:
  "0 < of_int z \<longleftrightarrow> 0 < z"
  using of_int_less_iff [of 0 z] by simp

lemma of_int_less_0_iff [simp]:
  "of_int z < 0 \<longleftrightarrow> z < 0"
  using of_int_less_iff [of z 0] by simp

end

lemma of_int_eq_id [simp]: "of_int = id"
proof
  fix z show "of_int z = id z"
    by (cases z rule: int_diff_cases, simp)
qed


subsection {* Magnitude of an Integer, as a Natural Number: @{text nat} *}

lift_definition nat :: "int \<Rightarrow> nat" is "\<lambda>(x, y). x - y"
  by auto

lemma nat_int [simp]: "nat (int n) = n"
  by transfer simp

lemma int_nat_eq [simp]: "int (nat z) = (if 0 \<le> z then z else 0)"
  by transfer clarsimp

corollary nat_0_le: "0 \<le> z ==> int (nat z) = z"
by simp

lemma nat_le_0 [simp]: "z \<le> 0 ==> nat z = 0"
  by transfer clarsimp

lemma nat_le_eq_zle: "0 < w | 0 \<le> z ==> (nat w \<le> nat z) = (w\<le>z)"
  by transfer (clarsimp, arith)

text{*An alternative condition is @{term "0 \<le> w"} *}
corollary nat_mono_iff: "0 < z ==> (nat w < nat z) = (w < z)"
by (simp add: nat_le_eq_zle linorder_not_le [symmetric]) 

corollary nat_less_eq_zless: "0 \<le> w ==> (nat w < nat z) = (w<z)"
by (simp add: nat_le_eq_zle linorder_not_le [symmetric]) 

lemma zless_nat_conj [simp]: "(nat w < nat z) = (0 < z & w < z)"
  by transfer (clarsimp, arith)

lemma nonneg_eq_int:
  fixes z :: int
  assumes "0 \<le> z" and "\<And>m. z = int m \<Longrightarrow> P"
  shows P
  using assms by (blast dest: nat_0_le sym)

lemma nat_eq_iff: "(nat w = m) = (if 0 \<le> w then w = int m else m=0)"
  by transfer (clarsimp simp add: le_imp_diff_is_add)

corollary nat_eq_iff2: "(m = nat w) = (if 0 \<le> w then w = int m else m=0)"
by (simp only: eq_commute [of m] nat_eq_iff)

lemma nat_less_iff: "0 \<le> w ==> (nat w < m) = (w < of_nat m)"
  by transfer (clarsimp, arith)

lemma nat_le_iff: "nat x \<le> n \<longleftrightarrow> x \<le> int n"
  by transfer (clarsimp simp add: le_diff_conv)

lemma nat_mono: "x \<le> y \<Longrightarrow> nat x \<le> nat y"
  by transfer auto

lemma nat_0_iff[simp]: "nat(i::int) = 0 \<longleftrightarrow> i\<le>0"
  by transfer clarsimp

lemma int_eq_iff: "(of_nat m = z) = (m = nat z & 0 \<le> z)"
by (auto simp add: nat_eq_iff2)

lemma zero_less_nat_eq [simp]: "(0 < nat z) = (0 < z)"
by (insert zless_nat_conj [of 0], auto)

lemma nat_add_distrib:
     "[| (0::int) \<le> z;  0 \<le> z' |] ==> nat (z+z') = nat z + nat z'"
  by transfer clarsimp

lemma nat_diff_distrib:
     "[| (0::int) \<le> z';  z' \<le> z |] ==> nat (z-z') = nat z - nat z'"
  by transfer clarsimp

lemma nat_zminus_int [simp]: "nat (- int n) = 0"
  by transfer simp

lemma zless_nat_eq_int_zless: "(m < nat z) = (int m < z)"
  by transfer (clarsimp simp add: less_diff_conv)

context ring_1
begin

lemma of_nat_nat: "0 \<le> z \<Longrightarrow> of_nat (nat z) = of_int z"
  by transfer (clarsimp simp add: of_nat_diff)

end

text {* For termination proofs: *}
lemma measure_function_int[measure_function]: "is_measure (nat o abs)" ..


subsection{*Lemmas about the Function @{term of_nat} and Orderings*}

lemma negative_zless_0: "- (int (Suc n)) < (0 \<Colon> int)"
by (simp add: order_less_le del: of_nat_Suc)

lemma negative_zless [iff]: "- (int (Suc n)) < int m"
by (rule negative_zless_0 [THEN order_less_le_trans], simp)

lemma negative_zle_0: "- int n \<le> 0"
by (simp add: minus_le_iff)

lemma negative_zle [iff]: "- int n \<le> int m"
by (rule order_trans [OF negative_zle_0 of_nat_0_le_iff])

lemma not_zle_0_negative [simp]: "~ (0 \<le> - (int (Suc n)))"
by (subst le_minus_iff, simp del: of_nat_Suc)

lemma int_zle_neg: "(int n \<le> - int m) = (n = 0 & m = 0)"
  by transfer simp

lemma not_int_zless_negative [simp]: "~ (int n < - int m)"
by (simp add: linorder_not_less)

lemma negative_eq_positive [simp]: "(- int n = of_nat m) = (n = 0 & m = 0)"
by (force simp add: order_eq_iff [of "- of_nat n"] int_zle_neg)

lemma zle_iff_zadd: "w \<le> z \<longleftrightarrow> (\<exists>n. z = w + int n)"
proof -
  have "(w \<le> z) = (0 \<le> z - w)"
    by (simp only: le_diff_eq add_0_left)
  also have "\<dots> = (\<exists>n. z - w = of_nat n)"
    by (auto elim: zero_le_imp_eq_int)
  also have "\<dots> = (\<exists>n. z = w + of_nat n)"
    by (simp only: algebra_simps)
  finally show ?thesis .
qed

lemma zadd_int_left: "int m + (int n + z) = int (m + n) + z"
by simp

lemma int_Suc0_eq_1: "int (Suc 0) = 1"
by simp

text{*This version is proved for all ordered rings, not just integers!
      It is proved here because attribute @{text arith_split} is not available
      in theory @{text Rings}.
      But is it really better than just rewriting with @{text abs_if}?*}
lemma abs_split [arith_split,no_atp]:
     "P(abs(a::'a::linordered_idom)) = ((0 \<le> a --> P a) & (a < 0 --> P(-a)))"
by (force dest: order_less_le_trans simp add: abs_if linorder_not_less)

lemma negD: "x < 0 \<Longrightarrow> \<exists>n. x = - (int (Suc n))"
apply transfer
apply clarsimp
apply (rule_tac x="b - Suc a" in exI, arith)
done


subsection {* Cases and induction *}

text{*Now we replace the case analysis rule by a more conventional one:
whether an integer is negative or not.*}

theorem int_cases [case_names nonneg neg, cases type: int]:
  "[|!! n. z = int n ==> P;  !! n. z =  - (int (Suc n)) ==> P |] ==> P"
apply (cases "z < 0")
apply (blast dest!: negD)
apply (simp add: linorder_not_less del: of_nat_Suc)
apply auto
apply (blast dest: nat_0_le [THEN sym])
done

theorem int_of_nat_induct [case_names nonneg neg, induct type: int]:
     "[|!! n. P (int n);  !!n. P (- (int (Suc n))) |] ==> P z"
  by (cases z) auto

lemma nonneg_int_cases:
  assumes "0 \<le> k" obtains n where "k = int n"
  using assms by (cases k, simp, simp del: of_nat_Suc)

lemma Let_numeral [simp]: "Let (numeral v) f = f (numeral v)"
  -- {* Unfold all @{text let}s involving constants *}
  unfolding Let_def ..

lemma Let_neg_numeral [simp]: "Let (neg_numeral v) f = f (neg_numeral v)"
  -- {* Unfold all @{text let}s involving constants *}
  unfolding Let_def ..

text {* Unfold @{text min} and @{text max} on numerals. *}

lemmas max_number_of [simp] =
  max_def [of "numeral u" "numeral v"]
  max_def [of "numeral u" "neg_numeral v"]
  max_def [of "neg_numeral u" "numeral v"]
  max_def [of "neg_numeral u" "neg_numeral v"] for u v

lemmas min_number_of [simp] =
  min_def [of "numeral u" "numeral v"]
  min_def [of "numeral u" "neg_numeral v"]
  min_def [of "neg_numeral u" "numeral v"]
  min_def [of "neg_numeral u" "neg_numeral v"] for u v


subsubsection {* Binary comparisons *}

text {* Preliminaries *}

lemma even_less_0_iff:
  "a + a < 0 \<longleftrightarrow> a < (0::'a::linordered_idom)"
proof -
  have "a + a < 0 \<longleftrightarrow> (1+1)*a < 0" by (simp add: left_distrib del: one_add_one)
  also have "(1+1)*a < 0 \<longleftrightarrow> a < 0"
    by (simp add: mult_less_0_iff zero_less_two 
                  order_less_not_sym [OF zero_less_two])
  finally show ?thesis .
qed

lemma le_imp_0_less: 
  assumes le: "0 \<le> z"
  shows "(0::int) < 1 + z"
proof -
  have "0 \<le> z" by fact
  also have "... < z + 1" by (rule less_add_one)
  also have "... = 1 + z" by (simp add: add_ac)
  finally show "0 < 1 + z" .
qed

lemma odd_less_0_iff:
  "(1 + z + z < 0) = (z < (0::int))"
proof (cases z)
  case (nonneg n)
  thus ?thesis by (simp add: linorder_not_less add_assoc add_increasing
                             le_imp_0_less [THEN order_less_imp_le])  
next
  case (neg n)
  thus ?thesis by (simp del: of_nat_Suc of_nat_add of_nat_1
    add: algebra_simps of_nat_1 [where 'a=int, symmetric] of_nat_add [symmetric])
qed

subsubsection {* Comparisons, for Ordered Rings *}

lemmas double_eq_0_iff = double_zero

lemma odd_nonzero:
  "1 + z + z \<noteq> (0::int)"
proof (cases z)
  case (nonneg n)
  have le: "0 \<le> z+z" by (simp add: nonneg add_increasing) 
  thus ?thesis using  le_imp_0_less [OF le]
    by (auto simp add: add_assoc) 
next
  case (neg n)
  show ?thesis
  proof
    assume eq: "1 + z + z = 0"
    have "(0::int) < 1 + (int n + int n)"
      by (simp add: le_imp_0_less add_increasing) 
    also have "... = - (1 + z + z)" 
      by (simp add: neg add_assoc [symmetric]) 
    also have "... = 0" by (simp add: eq) 
    finally have "0<0" ..
    thus False by blast
  qed
qed


subsection {* The Set of Integers *}

context ring_1
begin

definition Ints  :: "'a set" where
  "Ints = range of_int"

notation (xsymbols)
  Ints  ("\<int>")

lemma Ints_of_int [simp]: "of_int z \<in> \<int>"
  by (simp add: Ints_def)

lemma Ints_of_nat [simp]: "of_nat n \<in> \<int>"
  using Ints_of_int [of "of_nat n"] by simp

lemma Ints_0 [simp]: "0 \<in> \<int>"
  using Ints_of_int [of "0"] by simp

lemma Ints_1 [simp]: "1 \<in> \<int>"
  using Ints_of_int [of "1"] by simp

lemma Ints_add [simp]: "a \<in> \<int> \<Longrightarrow> b \<in> \<int> \<Longrightarrow> a + b \<in> \<int>"
apply (auto simp add: Ints_def)
apply (rule range_eqI)
apply (rule of_int_add [symmetric])
done

lemma Ints_minus [simp]: "a \<in> \<int> \<Longrightarrow> -a \<in> \<int>"
apply (auto simp add: Ints_def)
apply (rule range_eqI)
apply (rule of_int_minus [symmetric])
done

lemma Ints_diff [simp]: "a \<in> \<int> \<Longrightarrow> b \<in> \<int> \<Longrightarrow> a - b \<in> \<int>"
apply (auto simp add: Ints_def)
apply (rule range_eqI)
apply (rule of_int_diff [symmetric])
done

lemma Ints_mult [simp]: "a \<in> \<int> \<Longrightarrow> b \<in> \<int> \<Longrightarrow> a * b \<in> \<int>"
apply (auto simp add: Ints_def)
apply (rule range_eqI)
apply (rule of_int_mult [symmetric])
done

lemma Ints_power [simp]: "a \<in> \<int> \<Longrightarrow> a ^ n \<in> \<int>"
by (induct n) simp_all

lemma Ints_cases [cases set: Ints]:
  assumes "q \<in> \<int>"
  obtains (of_int) z where "q = of_int z"
  unfolding Ints_def
proof -
  from `q \<in> \<int>` have "q \<in> range of_int" unfolding Ints_def .
  then obtain z where "q = of_int z" ..
  then show thesis ..
qed

lemma Ints_induct [case_names of_int, induct set: Ints]:
  "q \<in> \<int> \<Longrightarrow> (\<And>z. P (of_int z)) \<Longrightarrow> P q"
  by (rule Ints_cases) auto

end

text {* The premise involving @{term Ints} prevents @{term "a = 1/2"}. *}

lemma Ints_double_eq_0_iff:
  assumes in_Ints: "a \<in> Ints"
  shows "(a + a = 0) = (a = (0::'a::ring_char_0))"
proof -
  from in_Ints have "a \<in> range of_int" unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  show ?thesis
  proof
    assume "a = 0"
    thus "a + a = 0" by simp
  next
    assume eq: "a + a = 0"
    hence "of_int (z + z) = (of_int 0 :: 'a)" by (simp add: a)
    hence "z + z = 0" by (simp only: of_int_eq_iff)
    hence "z = 0" by (simp only: double_eq_0_iff)
    thus "a = 0" by (simp add: a)
  qed
qed

lemma Ints_odd_nonzero:
  assumes in_Ints: "a \<in> Ints"
  shows "1 + a + a \<noteq> (0::'a::ring_char_0)"
proof -
  from in_Ints have "a \<in> range of_int" unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  show ?thesis
  proof
    assume eq: "1 + a + a = 0"
    hence "of_int (1 + z + z) = (of_int 0 :: 'a)" by (simp add: a)
    hence "1 + z + z = 0" by (simp only: of_int_eq_iff)
    with odd_nonzero show False by blast
  qed
qed 

lemma Nats_numeral [simp]: "numeral w \<in> Nats"
  using of_nat_in_Nats [of "numeral w"] by simp

lemma Ints_odd_less_0: 
  assumes in_Ints: "a \<in> Ints"
  shows "(1 + a + a < 0) = (a < (0::'a::linordered_idom))"
proof -
  from in_Ints have "a \<in> range of_int" unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  hence "((1::'a) + a + a < 0) = (of_int (1 + z + z) < (of_int 0 :: 'a))"
    by (simp add: a)
  also have "... = (z < 0)" by (simp only: of_int_less_iff odd_less_0_iff)
  also have "... = (a < 0)" by (simp add: a)
  finally show ?thesis .
qed


subsection {* @{term setsum} and @{term setprod} *}

lemma of_nat_setsum: "of_nat (setsum f A) = (\<Sum>x\<in>A. of_nat(f x))"
  apply (cases "finite A")
  apply (erule finite_induct, auto)
  done

lemma of_int_setsum: "of_int (setsum f A) = (\<Sum>x\<in>A. of_int(f x))"
  apply (cases "finite A")
  apply (erule finite_induct, auto)
  done

lemma of_nat_setprod: "of_nat (setprod f A) = (\<Prod>x\<in>A. of_nat(f x))"
  apply (cases "finite A")
  apply (erule finite_induct, auto simp add: of_nat_mult)
  done

lemma of_int_setprod: "of_int (setprod f A) = (\<Prod>x\<in>A. of_int(f x))"
  apply (cases "finite A")
  apply (erule finite_induct, auto)
  done

lemmas int_setsum = of_nat_setsum [where 'a=int]
lemmas int_setprod = of_nat_setprod [where 'a=int]


text {* Legacy theorems *}

lemmas zle_int = of_nat_le_iff [where 'a=int]
lemmas int_int_eq = of_nat_eq_iff [where 'a=int]
lemmas numeral_1_eq_1 = numeral_One

subsection {* Setting up simplification procedures *}

lemmas int_arith_rules =
  neg_le_iff_le numeral_One
  minus_zero diff_minus left_minus right_minus
  mult_zero_left mult_zero_right mult_1_left mult_1_right
  mult_minus_left mult_minus_right
  minus_add_distrib minus_minus mult_assoc
  of_nat_0 of_nat_1 of_nat_Suc of_nat_add of_nat_mult
  of_int_0 of_int_1 of_int_add of_int_mult

ML_file "Tools/int_arith.ML"
declaration {* K Int_Arith.setup *}

simproc_setup fast_arith ("(m::'a::linordered_idom) < n" |
  "(m::'a::linordered_idom) <= n" |
  "(m::'a::linordered_idom) = n") =
  {* fn _ => fn ss => fn ct => Lin_Arith.simproc ss (term_of ct) *}


subsection{*Lemmas About Small Numerals*}

lemma abs_power_minus_one [simp]:
  "abs(-1 ^ n) = (1::'a::linordered_idom)"
by (simp add: power_abs)


subsection{*More Inequality Reasoning*}

lemma zless_add1_eq: "(w < z + (1::int)) = (w<z | w=z)"
by arith

lemma add1_zle_eq: "(w + (1::int) \<le> z) = (w<z)"
by arith

lemma zle_diff1_eq [simp]: "(w \<le> z - (1::int)) = (w<z)"
by arith

lemma zle_add1_eq_le [simp]: "(w < z + (1::int)) = (w\<le>z)"
by arith

lemma int_one_le_iff_zero_less: "((1::int) \<le> z) = (0 < z)"
by arith


subsection{*The functions @{term nat} and @{term int}*}

text{*Simplify the term @{term "w + - z"}*}
lemmas diff_int_def_symmetric = diff_def [where 'a=int, symmetric, simp]

lemma nat_0 [simp]: "nat 0 = 0"
by (simp add: nat_eq_iff)

lemma nat_1 [simp]: "nat 1 = Suc 0"
by (subst nat_eq_iff, simp)

lemma nat_2: "nat 2 = Suc (Suc 0)"
by (subst nat_eq_iff, simp)

lemma one_less_nat_eq [simp]: "(Suc 0 < nat z) = (1 < z)"
apply (insert zless_nat_conj [of 1 z])
apply auto
done

text{*This simplifies expressions of the form @{term "int n = z"} where
      z is an integer literal.*}
lemmas int_eq_iff_numeral [simp] = int_eq_iff [of _ "numeral v"] for v

lemma split_nat [arith_split]:
  "P(nat(i::int)) = ((\<forall>n. i = int n \<longrightarrow> P n) & (i < 0 \<longrightarrow> P 0))"
  (is "?P = (?L & ?R)")
proof (cases "i < 0")
  case True thus ?thesis by auto
next
  case False
  have "?P = ?L"
  proof
    assume ?P thus ?L using False by clarsimp
  next
    assume ?L thus ?P using False by simp
  qed
  with False show ?thesis by simp
qed

context ring_1
begin

lemma of_int_of_nat [nitpick_simp]:
  "of_int k = (if k < 0 then - of_nat (nat (- k)) else of_nat (nat k))"
proof (cases "k < 0")
  case True then have "0 \<le> - k" by simp
  then have "of_nat (nat (- k)) = of_int (- k)" by (rule of_nat_nat)
  with True show ?thesis by simp
next
  case False then show ?thesis by (simp add: not_less of_nat_nat)
qed

end

lemma nat_mult_distrib:
  fixes z z' :: int
  assumes "0 \<le> z"
  shows "nat (z * z') = nat z * nat z'"
proof (cases "0 \<le> z'")
  case False with assms have "z * z' \<le> 0"
    by (simp add: not_le mult_le_0_iff)
  then have "nat (z * z') = 0" by simp
  moreover from False have "nat z' = 0" by simp
  ultimately show ?thesis by simp
next
  case True with assms have ge_0: "z * z' \<ge> 0" by (simp add: zero_le_mult_iff)
  show ?thesis
    by (rule injD [of "of_nat :: nat \<Rightarrow> int", OF inj_of_nat])
      (simp only: of_nat_mult of_nat_nat [OF True]
         of_nat_nat [OF assms] of_nat_nat [OF ge_0], simp)
qed

lemma nat_mult_distrib_neg: "z \<le> (0::int) ==> nat(z*z') = nat(-z) * nat(-z')"
apply (rule trans)
apply (rule_tac [2] nat_mult_distrib, auto)
done

lemma nat_abs_mult_distrib: "nat (abs (w * z)) = nat (abs w) * nat (abs z)"
apply (cases "z=0 | w=0")
apply (auto simp add: abs_if nat_mult_distrib [symmetric] 
                      nat_mult_distrib_neg [symmetric] mult_less_0_iff)
done

lemma Suc_nat_eq_nat_zadd1: "(0::int) <= z ==> Suc (nat z) = nat (1 + z)"
apply (rule sym)
apply (simp add: nat_eq_iff)
done

lemma diff_nat_eq_if:
     "nat z - nat z' =  
        (if z' < 0 then nat z   
         else let d = z-z' in     
              if d < 0 then 0 else nat d)"
by (simp add: Let_def nat_diff_distrib [symmetric])

(* nat_diff_distrib has too-strong premises *)
lemma nat_diff_distrib': "\<lbrakk>0 \<le> x; 0 \<le> y\<rbrakk> \<Longrightarrow> nat (x - y) = nat x - nat y"
apply (rule int_int_eq [THEN iffD1], clarsimp)
apply (subst of_nat_diff)
apply (rule nat_mono, simp_all)
done

lemma nat_numeral [simp, code_abbrev]:
  "nat (numeral k) = numeral k"
  by (simp add: nat_eq_iff)

lemma nat_neg_numeral [simp]:
  "nat (neg_numeral k) = 0"
  by simp

lemma diff_nat_numeral [simp]: 
  "(numeral v :: nat) - numeral v' = nat (numeral v - numeral v')"
  by (simp only: nat_diff_distrib' zero_le_numeral nat_numeral)

lemma nat_numeral_diff_1 [simp]:
  "numeral v - (1::nat) = nat (numeral v - 1)"
  using diff_nat_numeral [of v Num.One] by simp

lemmas nat_arith = diff_nat_numeral


subsection "Induction principles for int"

text{*Well-founded segments of the integers*}

definition
  int_ge_less_than  ::  "int => (int * int) set"
where
  "int_ge_less_than d = {(z',z). d \<le> z' & z' < z}"

theorem wf_int_ge_less_than: "wf (int_ge_less_than d)"
proof -
  have "int_ge_less_than d \<subseteq> measure (%z. nat (z-d))"
    by (auto simp add: int_ge_less_than_def)
  thus ?thesis 
    by (rule wf_subset [OF wf_measure]) 
qed

text{*This variant looks odd, but is typical of the relations suggested
by RankFinder.*}

definition
  int_ge_less_than2 ::  "int => (int * int) set"
where
  "int_ge_less_than2 d = {(z',z). d \<le> z & z' < z}"

theorem wf_int_ge_less_than2: "wf (int_ge_less_than2 d)"
proof -
  have "int_ge_less_than2 d \<subseteq> measure (%z. nat (1+z-d))" 
    by (auto simp add: int_ge_less_than2_def)
  thus ?thesis 
    by (rule wf_subset [OF wf_measure]) 
qed

(* `set:int': dummy construction *)
theorem int_ge_induct [case_names base step, induct set: int]:
  fixes i :: int
  assumes ge: "k \<le> i" and
    base: "P k" and
    step: "\<And>i. k \<le> i \<Longrightarrow> P i \<Longrightarrow> P (i + 1)"
  shows "P i"
proof -
  { fix n
    have "\<And>i::int. n = nat (i - k) \<Longrightarrow> k \<le> i \<Longrightarrow> P i"
    proof (induct n)
      case 0
      hence "i = k" by arith
      thus "P i" using base by simp
    next
      case (Suc n)
      then have "n = nat((i - 1) - k)" by arith
      moreover
      have ki1: "k \<le> i - 1" using Suc.prems by arith
      ultimately
      have "P (i - 1)" by (rule Suc.hyps)
      from step [OF ki1 this] show ?case by simp
    qed
  }
  with ge show ?thesis by fast
qed

(* `set:int': dummy construction *)
theorem int_gr_induct [case_names base step, induct set: int]:
  assumes gr: "k < (i::int)" and
        base: "P(k+1)" and
        step: "\<And>i. \<lbrakk>k < i; P i\<rbrakk> \<Longrightarrow> P(i+1)"
  shows "P i"
apply(rule int_ge_induct[of "k + 1"])
  using gr apply arith
 apply(rule base)
apply (rule step, simp+)
done

theorem int_le_induct [consumes 1, case_names base step]:
  assumes le: "i \<le> (k::int)" and
        base: "P(k)" and
        step: "\<And>i. \<lbrakk>i \<le> k; P i\<rbrakk> \<Longrightarrow> P(i - 1)"
  shows "P i"
proof -
  { fix n
    have "\<And>i::int. n = nat(k-i) \<Longrightarrow> i \<le> k \<Longrightarrow> P i"
    proof (induct n)
      case 0
      hence "i = k" by arith
      thus "P i" using base by simp
    next
      case (Suc n)
      hence "n = nat (k - (i + 1))" by arith
      moreover
      have ki1: "i + 1 \<le> k" using Suc.prems by arith
      ultimately
      have "P (i + 1)" by(rule Suc.hyps)
      from step[OF ki1 this] show ?case by simp
    qed
  }
  with le show ?thesis by fast
qed

theorem int_less_induct [consumes 1, case_names base step]:
  assumes less: "(i::int) < k" and
        base: "P(k - 1)" and
        step: "\<And>i. \<lbrakk>i < k; P i\<rbrakk> \<Longrightarrow> P(i - 1)"
  shows "P i"
apply(rule int_le_induct[of _ "k - 1"])
  using less apply arith
 apply(rule base)
apply (rule step, simp+)
done

theorem int_induct [case_names base step1 step2]:
  fixes k :: int
  assumes base: "P k"
    and step1: "\<And>i. k \<le> i \<Longrightarrow> P i \<Longrightarrow> P (i + 1)"
    and step2: "\<And>i. k \<ge> i \<Longrightarrow> P i \<Longrightarrow> P (i - 1)"
  shows "P i"
proof -
  have "i \<le> k \<or> i \<ge> k" by arith
  then show ?thesis
  proof
    assume "i \<ge> k"
    then show ?thesis using base
      by (rule int_ge_induct) (fact step1)
  next
    assume "i \<le> k"
    then show ?thesis using base
      by (rule int_le_induct) (fact step2)
  qed
qed

subsection{*Intermediate value theorems*}

lemma int_val_lemma:
     "(\<forall>i<n::nat. abs(f(i+1) - f i) \<le> 1) -->  
      f 0 \<le> k --> k \<le> f n --> (\<exists>i \<le> n. f i = (k::int))"
unfolding One_nat_def
apply (induct n)
apply simp
apply (intro strip)
apply (erule impE, simp)
apply (erule_tac x = n in allE, simp)
apply (case_tac "k = f (Suc n)")
apply force
apply (erule impE)
 apply (simp add: abs_if split add: split_if_asm)
apply (blast intro: le_SucI)
done

lemmas nat0_intermed_int_val = int_val_lemma [rule_format (no_asm)]

lemma nat_intermed_int_val:
     "[| \<forall>i. m \<le> i & i < n --> abs(f(i + 1::nat) - f i) \<le> 1; m < n;  
         f m \<le> k; k \<le> f n |] ==> ? i. m \<le> i & i \<le> n & f i = (k::int)"
apply (cut_tac n = "n-m" and f = "%i. f (i+m) " and k = k 
       in int_val_lemma)
unfolding One_nat_def
apply simp
apply (erule exE)
apply (rule_tac x = "i+m" in exI, arith)
done


subsection{*Products and 1, by T. M. Rasmussen*}

lemma zabs_less_one_iff [simp]: "(\<bar>z\<bar> < 1) = (z = (0::int))"
by arith

lemma abs_zmult_eq_1:
  assumes mn: "\<bar>m * n\<bar> = 1"
  shows "\<bar>m\<bar> = (1::int)"
proof -
  have 0: "m \<noteq> 0 & n \<noteq> 0" using mn
    by auto
  have "~ (2 \<le> \<bar>m\<bar>)"
  proof
    assume "2 \<le> \<bar>m\<bar>"
    hence "2*\<bar>n\<bar> \<le> \<bar>m\<bar>*\<bar>n\<bar>"
      by (simp add: mult_mono 0) 
    also have "... = \<bar>m*n\<bar>" 
      by (simp add: abs_mult)
    also have "... = 1"
      by (simp add: mn)
    finally have "2*\<bar>n\<bar> \<le> 1" .
    thus "False" using 0
      by arith
  qed
  thus ?thesis using 0
    by auto
qed

ML_val {* @{const_name neg_numeral} *}

lemma pos_zmult_eq_1_iff_lemma: "(m * n = 1) ==> m = (1::int) | m = -1"
by (insert abs_zmult_eq_1 [of m n], arith)

lemma pos_zmult_eq_1_iff:
  assumes "0 < (m::int)" shows "(m * n = 1) = (m = 1 & n = 1)"
proof -
  from assms have "m * n = 1 ==> m = 1" by (auto dest: pos_zmult_eq_1_iff_lemma)
  thus ?thesis by (auto dest: pos_zmult_eq_1_iff_lemma)
qed

lemma zmult_eq_1_iff: "(m*n = (1::int)) = ((m = 1 & n = 1) | (m = -1 & n = -1))"
apply (rule iffI) 
 apply (frule pos_zmult_eq_1_iff_lemma)
 apply (simp add: mult_commute [of m]) 
 apply (frule pos_zmult_eq_1_iff_lemma, auto) 
done

lemma infinite_UNIV_int: "\<not> finite (UNIV::int set)"
proof
  assume "finite (UNIV::int set)"
  moreover have "inj (\<lambda>i\<Colon>int. 2 * i)"
    by (rule injI) simp
  ultimately have "surj (\<lambda>i\<Colon>int. 2 * i)"
    by (rule finite_UNIV_inj_surj)
  then obtain i :: int where "1 = 2 * i" by (rule surjE)
  then show False by (simp add: pos_zmult_eq_1_iff)
qed


subsection {* Further theorems on numerals *}

subsubsection{*Special Simplification for Constants*}

text{*These distributive laws move literals inside sums and differences.*}

lemmas left_distrib_numeral [simp] = left_distrib [of _ _ "numeral v"] for v
lemmas right_distrib_numeral [simp] = right_distrib [of "numeral v"] for v
lemmas left_diff_distrib_numeral [simp] = left_diff_distrib [of _ _ "numeral v"] for v
lemmas right_diff_distrib_numeral [simp] = right_diff_distrib [of "numeral v"] for v

text{*These are actually for fields, like real: but where else to put them?*}

lemmas zero_less_divide_iff_numeral [simp, no_atp] = zero_less_divide_iff [of "numeral w"] for w
lemmas divide_less_0_iff_numeral [simp, no_atp] = divide_less_0_iff [of "numeral w"] for w
lemmas zero_le_divide_iff_numeral [simp, no_atp] = zero_le_divide_iff [of "numeral w"] for w
lemmas divide_le_0_iff_numeral [simp, no_atp] = divide_le_0_iff [of "numeral w"] for w


text {*Replaces @{text "inverse #nn"} by @{text "1/#nn"}.  It looks
  strange, but then other simprocs simplify the quotient.*}

lemmas inverse_eq_divide_numeral [simp] =
  inverse_eq_divide [of "numeral w"] for w

lemmas inverse_eq_divide_neg_numeral [simp] =
  inverse_eq_divide [of "neg_numeral w"] for w

text {*These laws simplify inequalities, moving unary minus from a term
into the literal.*}

lemmas le_minus_iff_numeral [simp, no_atp] =
  le_minus_iff [of "numeral v"]
  le_minus_iff [of "neg_numeral v"] for v

lemmas equation_minus_iff_numeral [simp, no_atp] =
  equation_minus_iff [of "numeral v"]
  equation_minus_iff [of "neg_numeral v"] for v

lemmas minus_less_iff_numeral [simp, no_atp] =
  minus_less_iff [of _ "numeral v"]
  minus_less_iff [of _ "neg_numeral v"] for v

lemmas minus_le_iff_numeral [simp, no_atp] =
  minus_le_iff [of _ "numeral v"]
  minus_le_iff [of _ "neg_numeral v"] for v

lemmas minus_equation_iff_numeral [simp, no_atp] =
  minus_equation_iff [of _ "numeral v"]
  minus_equation_iff [of _ "neg_numeral v"] for v

text{*To Simplify Inequalities Where One Side is the Constant 1*}

lemma less_minus_iff_1 [simp,no_atp]:
  fixes b::"'b::linordered_idom"
  shows "(1 < - b) = (b < -1)"
by auto

lemma le_minus_iff_1 [simp,no_atp]:
  fixes b::"'b::linordered_idom"
  shows "(1 \<le> - b) = (b \<le> -1)"
by auto

lemma equation_minus_iff_1 [simp,no_atp]:
  fixes b::"'b::ring_1"
  shows "(1 = - b) = (b = -1)"
by (subst equation_minus_iff, auto)

lemma minus_less_iff_1 [simp,no_atp]:
  fixes a::"'b::linordered_idom"
  shows "(- a < 1) = (-1 < a)"
by auto

lemma minus_le_iff_1 [simp,no_atp]:
  fixes a::"'b::linordered_idom"
  shows "(- a \<le> 1) = (-1 \<le> a)"
by auto

lemma minus_equation_iff_1 [simp,no_atp]:
  fixes a::"'b::ring_1"
  shows "(- a = 1) = (a = -1)"
by (subst minus_equation_iff, auto)


text {*Cancellation of constant factors in comparisons (@{text "<"} and @{text "\<le>"}) *}

lemmas mult_less_cancel_left_numeral [simp, no_atp] = mult_less_cancel_left [of "numeral v"] for v
lemmas mult_less_cancel_right_numeral [simp, no_atp] = mult_less_cancel_right [of _ "numeral v"] for v
lemmas mult_le_cancel_left_numeral [simp, no_atp] = mult_le_cancel_left [of "numeral v"] for v
lemmas mult_le_cancel_right_numeral [simp, no_atp] = mult_le_cancel_right [of _ "numeral v"] for v


text {*Multiplying out constant divisors in comparisons (@{text "<"}, @{text "\<le>"} and @{text "="}) *}

lemmas le_divide_eq_numeral1 [simp] =
  pos_le_divide_eq [of "numeral w", OF zero_less_numeral]
  neg_le_divide_eq [of "neg_numeral w", OF neg_numeral_less_zero] for w

lemmas divide_le_eq_numeral1 [simp] =
  pos_divide_le_eq [of "numeral w", OF zero_less_numeral]
  neg_divide_le_eq [of "neg_numeral w", OF neg_numeral_less_zero] for w

lemmas less_divide_eq_numeral1 [simp] =
  pos_less_divide_eq [of "numeral w", OF zero_less_numeral]
  neg_less_divide_eq [of "neg_numeral w", OF neg_numeral_less_zero] for w

lemmas divide_less_eq_numeral1 [simp] =
  pos_divide_less_eq [of "numeral w", OF zero_less_numeral]
  neg_divide_less_eq [of "neg_numeral w", OF neg_numeral_less_zero] for w

lemmas eq_divide_eq_numeral1 [simp] =
  eq_divide_eq [of _ _ "numeral w"]
  eq_divide_eq [of _ _ "neg_numeral w"] for w

lemmas divide_eq_eq_numeral1 [simp] =
  divide_eq_eq [of _ "numeral w"]
  divide_eq_eq [of _ "neg_numeral w"] for w

subsubsection{*Optional Simplification Rules Involving Constants*}

text{*Simplify quotients that are compared with a literal constant.*}

lemmas le_divide_eq_numeral =
  le_divide_eq [of "numeral w"]
  le_divide_eq [of "neg_numeral w"] for w

lemmas divide_le_eq_numeral =
  divide_le_eq [of _ _ "numeral w"]
  divide_le_eq [of _ _ "neg_numeral w"] for w

lemmas less_divide_eq_numeral =
  less_divide_eq [of "numeral w"]
  less_divide_eq [of "neg_numeral w"] for w

lemmas divide_less_eq_numeral =
  divide_less_eq [of _ _ "numeral w"]
  divide_less_eq [of _ _ "neg_numeral w"] for w

lemmas eq_divide_eq_numeral =
  eq_divide_eq [of "numeral w"]
  eq_divide_eq [of "neg_numeral w"] for w

lemmas divide_eq_eq_numeral =
  divide_eq_eq [of _ _ "numeral w"]
  divide_eq_eq [of _ _ "neg_numeral w"] for w


text{*Not good as automatic simprules because they cause case splits.*}
lemmas divide_const_simps =
  le_divide_eq_numeral divide_le_eq_numeral less_divide_eq_numeral
  divide_less_eq_numeral eq_divide_eq_numeral divide_eq_eq_numeral
  le_divide_eq_1 divide_le_eq_1 less_divide_eq_1 divide_less_eq_1

text{*Division By @{text "-1"}*}

lemma divide_minus1 [simp]: "(x::'a::field) / -1 = - x"
  unfolding minus_one [symmetric]
  unfolding nonzero_minus_divide_right [OF one_neq_zero, symmetric]
  by simp

lemma minus1_divide [simp]: "-1 / (x::'a::field) = - (1 / x)"
  unfolding minus_one [symmetric] by (rule divide_minus_left)

lemma half_gt_zero_iff:
     "(0 < r/2) = (0 < (r::'a::linordered_field_inverse_zero))"
by auto

lemmas half_gt_zero [simp] = half_gt_zero_iff [THEN iffD2]

lemma divide_Numeral1: "(x::'a::field) / Numeral1 = x"
  by simp


subsection {* The divides relation *}

lemma zdvd_antisym_nonneg:
    "0 <= m ==> 0 <= n ==> m dvd n ==> n dvd m ==> m = (n::int)"
  apply (simp add: dvd_def, auto)
  apply (auto simp add: mult_assoc zero_le_mult_iff zmult_eq_1_iff)
  done

lemma zdvd_antisym_abs: assumes "(a::int) dvd b" and "b dvd a" 
  shows "\<bar>a\<bar> = \<bar>b\<bar>"
proof cases
  assume "a = 0" with assms show ?thesis by simp
next
  assume "a \<noteq> 0"
  from `a dvd b` obtain k where k:"b = a*k" unfolding dvd_def by blast 
  from `b dvd a` obtain k' where k':"a = b*k'" unfolding dvd_def by blast 
  from k k' have "a = a*k*k'" by simp
  with mult_cancel_left1[where c="a" and b="k*k'"]
  have kk':"k*k' = 1" using `a\<noteq>0` by (simp add: mult_assoc)
  hence "k = 1 \<and> k' = 1 \<or> k = -1 \<and> k' = -1" by (simp add: zmult_eq_1_iff)
  thus ?thesis using k k' by auto
qed

lemma zdvd_zdiffD: "k dvd m - n ==> k dvd n ==> k dvd (m::int)"
  apply (subgoal_tac "m = n + (m - n)")
   apply (erule ssubst)
   apply (blast intro: dvd_add, simp)
  done

lemma zdvd_reduce: "(k dvd n + k * m) = (k dvd (n::int))"
apply (rule iffI)
 apply (erule_tac [2] dvd_add)
 apply (subgoal_tac "n = (n + k * m) - k * m")
  apply (erule ssubst)
  apply (erule dvd_diff)
  apply(simp_all)
done

lemma dvd_imp_le_int:
  fixes d i :: int
  assumes "i \<noteq> 0" and "d dvd i"
  shows "\<bar>d\<bar> \<le> \<bar>i\<bar>"
proof -
  from `d dvd i` obtain k where "i = d * k" ..
  with `i \<noteq> 0` have "k \<noteq> 0" by auto
  then have "1 \<le> \<bar>k\<bar>" and "0 \<le> \<bar>d\<bar>" by auto
  then have "\<bar>d\<bar> * 1 \<le> \<bar>d\<bar> * \<bar>k\<bar>" by (rule mult_left_mono)
  with `i = d * k` show ?thesis by (simp add: abs_mult)
qed

lemma zdvd_not_zless:
  fixes m n :: int
  assumes "0 < m" and "m < n"
  shows "\<not> n dvd m"
proof
  from assms have "0 < n" by auto
  assume "n dvd m" then obtain k where k: "m = n * k" ..
  with `0 < m` have "0 < n * k" by auto
  with `0 < n` have "0 < k" by (simp add: zero_less_mult_iff)
  with k `0 < n` `m < n` have "n * k < n * 1" by simp
  with `0 < n` `0 < k` show False unfolding mult_less_cancel_left by auto
qed

lemma zdvd_mult_cancel: assumes d:"k * m dvd k * n" and kz:"k \<noteq> (0::int)"
  shows "m dvd n"
proof-
  from d obtain h where h: "k*n = k*m * h" unfolding dvd_def by blast
  {assume "n \<noteq> m*h" hence "k* n \<noteq> k* (m*h)" using kz by simp
    with h have False by (simp add: mult_assoc)}
  hence "n = m * h" by blast
  thus ?thesis by simp
qed

theorem zdvd_int: "(x dvd y) = (int x dvd int y)"
proof -
  have "\<And>k. int y = int x * k \<Longrightarrow> x dvd y"
  proof -
    fix k
    assume A: "int y = int x * k"
    then show "x dvd y"
    proof (cases k)
      case (nonneg n)
      with A have "y = x * n" by (simp add: of_nat_mult [symmetric])
      then show ?thesis ..
    next
      case (neg n)
      with A have "int y = int x * (- int (Suc n))" by simp
      also have "\<dots> = - (int x * int (Suc n))" by (simp only: mult_minus_right)
      also have "\<dots> = - int (x * Suc n)" by (simp only: of_nat_mult [symmetric])
      finally have "- int (x * Suc n) = int y" ..
      then show ?thesis by (simp only: negative_eq_positive) auto
    qed
  qed
  then show ?thesis by (auto elim!: dvdE simp only: dvd_triv_left of_nat_mult)
qed

lemma zdvd1_eq[simp]: "(x::int) dvd 1 = (\<bar>x\<bar> = 1)"
proof
  assume d: "x dvd 1" hence "int (nat \<bar>x\<bar>) dvd int (nat 1)" by simp
  hence "nat \<bar>x\<bar> dvd 1" by (simp add: zdvd_int)
  hence "nat \<bar>x\<bar> = 1"  by simp
  thus "\<bar>x\<bar> = 1" by (cases "x < 0") auto
next
  assume "\<bar>x\<bar>=1"
  then have "x = 1 \<or> x = -1" by auto
  then show "x dvd 1" by (auto intro: dvdI)
qed

lemma zdvd_mult_cancel1: 
  assumes mp:"m \<noteq>(0::int)" shows "(m * n dvd m) = (\<bar>n\<bar> = 1)"
proof
  assume n1: "\<bar>n\<bar> = 1" thus "m * n dvd m" 
    by (cases "n >0") (auto simp add: minus_equation_iff)
next
  assume H: "m * n dvd m" hence H2: "m * n dvd m * 1" by simp
  from zdvd_mult_cancel[OF H2 mp] show "\<bar>n\<bar> = 1" by (simp only: zdvd1_eq)
qed

lemma int_dvd_iff: "(int m dvd z) = (m dvd nat (abs z))"
  unfolding zdvd_int by (cases "z \<ge> 0") simp_all

lemma dvd_int_iff: "(z dvd int m) = (nat (abs z) dvd m)"
  unfolding zdvd_int by (cases "z \<ge> 0") simp_all

lemma nat_dvd_iff: "(nat z dvd m) = (if 0 \<le> z then (z dvd int m) else m = 0)"
  by (auto simp add: dvd_int_iff)

lemma eq_nat_nat_iff:
  "0 \<le> z \<Longrightarrow> 0 \<le> z' \<Longrightarrow> nat z = nat z' \<longleftrightarrow> z = z'"
  by (auto elim!: nonneg_eq_int)

lemma nat_power_eq:
  "0 \<le> z \<Longrightarrow> nat (z ^ n) = nat z ^ n"
  by (induct n) (simp_all add: nat_mult_distrib)

lemma zdvd_imp_le: "[| z dvd n; 0 < n |] ==> z \<le> (n::int)"
  apply (cases n)
  apply (auto simp add: dvd_int_iff)
  apply (cases z)
  apply (auto simp add: dvd_imp_le)
  done

lemma zdvd_period:
  fixes a d :: int
  assumes "a dvd d"
  shows "a dvd (x + t) \<longleftrightarrow> a dvd ((x + c * d) + t)"
proof -
  from assms obtain k where "d = a * k" by (rule dvdE)
  show ?thesis
  proof
    assume "a dvd (x + t)"
    then obtain l where "x + t = a * l" by (rule dvdE)
    then have "x = a * l - t" by simp
    with `d = a * k` show "a dvd x + c * d + t" by simp
  next
    assume "a dvd x + c * d + t"
    then obtain l where "x + c * d + t = a * l" by (rule dvdE)
    then have "x = a * l - c * d - t" by simp
    with `d = a * k` show "a dvd (x + t)" by simp
  qed
qed


subsection {* Finiteness of intervals *}

lemma finite_interval_int1 [iff]: "finite {i :: int. a <= i & i <= b}"
proof (cases "a <= b")
  case True
  from this show ?thesis
  proof (induct b rule: int_ge_induct)
    case base
    have "{i. a <= i & i <= a} = {a}" by auto
    from this show ?case by simp
  next
    case (step b)
    from this have "{i. a <= i & i <= b + 1} = {i. a <= i & i <= b} \<union> {b + 1}" by auto
    from this step show ?case by simp
  qed
next
  case False from this show ?thesis
    by (metis (lifting, no_types) Collect_empty_eq finite.emptyI order_trans)
qed

lemma finite_interval_int2 [iff]: "finite {i :: int. a <= i & i < b}"
by (rule rev_finite_subset[OF finite_interval_int1[of "a" "b"]]) auto

lemma finite_interval_int3 [iff]: "finite {i :: int. a < i & i <= b}"
by (rule rev_finite_subset[OF finite_interval_int1[of "a" "b"]]) auto

lemma finite_interval_int4 [iff]: "finite {i :: int. a < i & i < b}"
by (rule rev_finite_subset[OF finite_interval_int1[of "a" "b"]]) auto


subsection {* Configuration of the code generator *}

text {* Constructors *}

definition Pos :: "num \<Rightarrow> int" where
  [simp, code_abbrev]: "Pos = numeral"

definition Neg :: "num \<Rightarrow> int" where
  [simp, code_abbrev]: "Neg = neg_numeral"

code_datatype "0::int" Pos Neg


text {* Auxiliary operations *}

definition dup :: "int \<Rightarrow> int" where
  [simp]: "dup k = k + k"

lemma dup_code [code]:
  "dup 0 = 0"
  "dup (Pos n) = Pos (Num.Bit0 n)"
  "dup (Neg n) = Neg (Num.Bit0 n)"
  unfolding Pos_def Neg_def neg_numeral_def
  by (simp_all add: numeral_Bit0)

definition sub :: "num \<Rightarrow> num \<Rightarrow> int" where
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
  by (simp_all only: algebra_simps)


text {* Implementations *}

lemma one_int_code [code, code_unfold]:
  "1 = Pos Num.One"
  by simp

lemma plus_int_code [code]:
  "k + 0 = (k::int)"
  "0 + l = (l::int)"
  "Pos m + Pos n = Pos (m + n)"
  "Pos m + Neg n = sub m n"
  "Neg m + Pos n = sub n m"
  "Neg m + Neg n = Neg (m + n)"
  by simp_all

lemma uminus_int_code [code]:
  "uminus 0 = (0::int)"
  "uminus (Pos m) = Neg m"
  "uminus (Neg m) = Pos m"
  by simp_all

lemma minus_int_code [code]:
  "k - 0 = (k::int)"
  "0 - l = uminus (l::int)"
  "Pos m - Pos n = sub m n"
  "Pos m - Neg n = Pos (m + n)"
  "Neg m - Pos n = Neg (m + n)"
  "Neg m - Neg n = sub n m"
  by simp_all

lemma times_int_code [code]:
  "k * 0 = (0::int)"
  "0 * l = (0::int)"
  "Pos m * Pos n = Pos (m * n)"
  "Pos m * Neg n = Neg (m * n)"
  "Neg m * Pos n = Neg (m * n)"
  "Neg m * Neg n = Pos (m * n)"
  by simp_all

instantiation int :: equal
begin

definition
  "HOL.equal k l \<longleftrightarrow> k = (l::int)"

instance by default (rule equal_int_def)

end

lemma equal_int_code [code]:
  "HOL.equal 0 (0::int) \<longleftrightarrow> True"
  "HOL.equal 0 (Pos l) \<longleftrightarrow> False"
  "HOL.equal 0 (Neg l) \<longleftrightarrow> False"
  "HOL.equal (Pos k) 0 \<longleftrightarrow> False"
  "HOL.equal (Pos k) (Pos l) \<longleftrightarrow> HOL.equal k l"
  "HOL.equal (Pos k) (Neg l) \<longleftrightarrow> False"
  "HOL.equal (Neg k) 0 \<longleftrightarrow> False"
  "HOL.equal (Neg k) (Pos l) \<longleftrightarrow> False"
  "HOL.equal (Neg k) (Neg l) \<longleftrightarrow> HOL.equal k l"
  by (auto simp add: equal)

lemma equal_int_refl [code nbe]:
  "HOL.equal (k::int) k \<longleftrightarrow> True"
  by (fact equal_refl)

lemma less_eq_int_code [code]:
  "0 \<le> (0::int) \<longleftrightarrow> True"
  "0 \<le> Pos l \<longleftrightarrow> True"
  "0 \<le> Neg l \<longleftrightarrow> False"
  "Pos k \<le> 0 \<longleftrightarrow> False"
  "Pos k \<le> Pos l \<longleftrightarrow> k \<le> l"
  "Pos k \<le> Neg l \<longleftrightarrow> False"
  "Neg k \<le> 0 \<longleftrightarrow> True"
  "Neg k \<le> Pos l \<longleftrightarrow> True"
  "Neg k \<le> Neg l \<longleftrightarrow> l \<le> k"
  by simp_all

lemma less_int_code [code]:
  "0 < (0::int) \<longleftrightarrow> False"
  "0 < Pos l \<longleftrightarrow> True"
  "0 < Neg l \<longleftrightarrow> False"
  "Pos k < 0 \<longleftrightarrow> False"
  "Pos k < Pos l \<longleftrightarrow> k < l"
  "Pos k < Neg l \<longleftrightarrow> False"
  "Neg k < 0 \<longleftrightarrow> True"
  "Neg k < Pos l \<longleftrightarrow> True"
  "Neg k < Neg l \<longleftrightarrow> l < k"
  by simp_all

lemma nat_code [code]:
  "nat (Int.Neg k) = 0"
  "nat 0 = 0"
  "nat (Int.Pos k) = nat_of_num k"
  by (simp_all add: nat_of_num_numeral nat_numeral)

lemma (in ring_1) of_int_code [code]:
  "of_int (Int.Neg k) = neg_numeral k"
  "of_int 0 = 0"
  "of_int (Int.Pos k) = numeral k"
  by simp_all


text {* Serializer setup *}

code_modulename SML
  Int Arith

code_modulename OCaml
  Int Arith

code_modulename Haskell
  Int Arith

quickcheck_params [default_type = int]

hide_const (open) Pos Neg sub dup


subsection {* Legacy theorems *}

lemmas inj_int = inj_of_nat [where 'a=int]
lemmas zadd_int = of_nat_add [where 'a=int, symmetric]
lemmas int_mult = of_nat_mult [where 'a=int]
lemmas zmult_int = of_nat_mult [where 'a=int, symmetric]
lemmas int_eq_0_conv = of_nat_eq_0_iff [where 'a=int and m="n"] for n
lemmas zless_int = of_nat_less_iff [where 'a=int]
lemmas int_less_0_conv = of_nat_less_0_iff [where 'a=int and m="k"] for k
lemmas zero_less_int_conv = of_nat_0_less_iff [where 'a=int]
lemmas zero_zle_int = of_nat_0_le_iff [where 'a=int]
lemmas int_le_0_conv = of_nat_le_0_iff [where 'a=int and m="n"] for n
lemmas int_0 = of_nat_0 [where 'a=int]
lemmas int_1 = of_nat_1 [where 'a=int]
lemmas int_Suc = of_nat_Suc [where 'a=int]
lemmas int_numeral = of_nat_numeral [where 'a=int]
lemmas abs_int_eq = abs_of_nat [where 'a=int and n="m"] for m
lemmas of_int_int_eq = of_int_of_nat_eq [where 'a=int]
lemmas zdiff_int = of_nat_diff [where 'a=int, symmetric]
lemmas zpower_numeral_even = power_numeral_even [where 'a=int]
lemmas zpower_numeral_odd = power_numeral_odd [where 'a=int]

lemma zpower_zpower:
  "(x ^ y) ^ z = (x ^ (y * z)::int)"
  by (rule power_mult [symmetric])

lemma int_power:
  "int (m ^ n) = int m ^ n"
  by (rule of_nat_power)

lemmas zpower_int = int_power [symmetric]

text {* De-register @{text "int"} as a quotient type: *}

lemmas [transfer_rule del] =
  int.id_abs_transfer int.rel_eq_transfer zero_int.transfer one_int.transfer
  plus_int.transfer uminus_int.transfer minus_int.transfer times_int.transfer
  int_transfer less_eq_int.transfer less_int.transfer of_int.transfer
  nat.transfer

declare Quotient_int [quot_del]

end
