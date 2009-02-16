(*  Title:      HOL/ex/Numeral.thy
    ID:         $Id$
    Author:     Florian Haftmann

An experimental alternative numeral representation.
*)

theory Numeral
imports Int Inductive
begin

subsection {* The @{text num} type *}

text {*
  We construct @{text num} as a copy of strictly positive
  natural numbers.
*}

typedef (open) num = "\<lambda>n\<Colon>nat. n > 0"
  morphisms nat_of_num num_of_nat_abs
  by (auto simp add: mem_def)

text {*
  A totalized abstraction function.  It is not entirely clear
  whether this is really useful.
*}

definition num_of_nat :: "nat \<Rightarrow> num" where
  "num_of_nat n = (if n = 0 then num_of_nat_abs 1 else num_of_nat_abs n)"

lemma num_cases [case_names nat, cases type: num]:
  assumes "(\<And>n\<Colon>nat. m = num_of_nat n \<Longrightarrow> 0 < n \<Longrightarrow> P)"
  shows P
apply (rule num_of_nat_abs_cases)
apply (unfold mem_def)
using assms unfolding num_of_nat_def
apply auto
done

lemma num_of_nat_zero: "num_of_nat 0 = num_of_nat 1"
  by (simp add: num_of_nat_def)

lemma num_of_nat_inverse: "nat_of_num (num_of_nat n) = (if n = 0 then 1 else n)"
  apply (simp add: num_of_nat_def)
  apply (subst num_of_nat_abs_inverse)
  apply (auto simp add: mem_def num_of_nat_abs_inverse)
  done

lemma num_of_nat_inject:
  "num_of_nat m = num_of_nat n \<longleftrightarrow> m = n \<or> (m = 0 \<or> m = 1) \<and> (n = 0 \<or> n = 1)"
by (auto simp add: num_of_nat_def num_of_nat_abs_inject [unfolded mem_def])

lemma split_num_all:
  "(\<And>m. PROP P m) \<equiv> (\<And>n. PROP P (num_of_nat n))"
proof
  fix n
  assume "\<And>m\<Colon>num. PROP P m"
  then show "PROP P (num_of_nat n)" .
next
  fix m
  have nat_of_num: "\<And>m. nat_of_num m \<noteq> 0"
    using nat_of_num by (auto simp add: mem_def)
  have nat_of_num_inverse: "\<And>m. num_of_nat (nat_of_num m) = m"
    by (auto simp add: num_of_nat_def nat_of_num_inverse nat_of_num)
  assume "\<And>n. PROP P (num_of_nat n)"
  then have "PROP P (num_of_nat (nat_of_num m))" .
  then show "PROP P m" unfolding nat_of_num_inverse .
qed


subsection {* Digit representation for @{typ num} *}

instantiation num :: "{semiring, monoid_mult}"
begin

definition one_num :: num where
  [code del]: "1 = num_of_nat 1"

definition plus_num :: "num \<Rightarrow> num \<Rightarrow> num" where
  [code del]: "m + n = num_of_nat (nat_of_num m + nat_of_num n)"

definition times_num :: "num \<Rightarrow> num \<Rightarrow> num" where
  [code del]: "m * n = num_of_nat (nat_of_num m * nat_of_num n)"

definition Dig0 :: "num \<Rightarrow> num" where
  [code del]: "Dig0 n = n + n"

definition Dig1 :: "num \<Rightarrow> num" where
  [code del]: "Dig1 n = n + n + 1"

instance proof
qed (simp_all add: one_num_def plus_num_def times_num_def
  split_num_all num_of_nat_inverse num_of_nat_zero add_ac mult_ac nat_distrib)

end

text {*
  The following proofs seem horribly complicated.
  Any room for simplification!?
*}

lemma nat_dig_cases [case_names 0 1 dig0 dig1]:
  fixes n :: nat
  assumes "n = 0 \<Longrightarrow> P"
  and "n = 1 \<Longrightarrow> P"
  and "\<And>m. m > 0 \<Longrightarrow> n = m + m \<Longrightarrow> P"
  and "\<And>m. m > 0 \<Longrightarrow> n = Suc (m + m) \<Longrightarrow> P"
  shows P
using assms proof (induct n)
  case 0 then show ?case by simp
next
  case (Suc n)
  show P proof (rule Suc.hyps)
    assume "n = 0"
    then have "Suc n = 1" by simp
    then show P by (rule Suc.prems(2))
  next
    assume "n = 1"
    have "1 > (0\<Colon>nat)" by simp
    moreover from `n = 1` have "Suc n = 1 + 1" by simp
    ultimately show P by (rule Suc.prems(3))
  next
    fix m
    assume "0 < m" and "n = m + m"
    note `0 < m`
    moreover from `n = m + m` have "Suc n = Suc (m + m)" by simp
    ultimately show P by (rule Suc.prems(4))
  next
    fix m
    assume "0 < m" and "n = Suc (m + m)"
    have "0 < Suc m" by simp
    moreover from `n = Suc (m + m)` have "Suc n = Suc m + Suc m" by simp
    ultimately show P by (rule Suc.prems(3))
  qed
qed

lemma num_induct_raw:
  fixes n :: nat
  assumes not0: "n > 0"
  assumes "P 1"
  and "\<And>n. n > 0 \<Longrightarrow> P n \<Longrightarrow> P (n + n)"
  and "\<And>n. n > 0 \<Longrightarrow> P n \<Longrightarrow> P (Suc (n + n))"
  shows "P n"
using not0 proof (induct n rule: less_induct)
  case (less n)
  show "P n" proof (cases n rule: nat_dig_cases)
    case 0 then show ?thesis using less by simp
  next
    case 1 then show ?thesis using assms by simp
  next
    case (dig0 m)
    then show ?thesis apply simp
      apply (rule assms(3)) apply assumption
      apply (rule less)
      apply simp_all
    done
  next
    case (dig1 m)
    then show ?thesis apply simp
      apply (rule assms(4)) apply assumption
      apply (rule less)
      apply simp_all
    done
  qed
qed

lemma num_of_nat_Suc: "num_of_nat (Suc n) = (if n = 0 then 1 else num_of_nat n + 1)"
  by (cases n) (auto simp add: one_num_def plus_num_def num_of_nat_inverse)

lemma num_induct [case_names 1 Suc, induct type: num]:
  fixes P :: "num \<Rightarrow> bool"
  assumes 1: "P 1"
    and Suc: "\<And>n. P n \<Longrightarrow> P (n + 1)"
  shows "P n"
proof (cases n)
  case (nat m) then show ?thesis by (induct m arbitrary: n)
    (auto simp: num_of_nat_Suc intro: 1 Suc split: split_if_asm)
qed

rep_datatype "1::num" Dig0 Dig1 proof -
  fix P m
  assume 1: "P 1"
    and Dig0: "\<And>m. P m \<Longrightarrow> P (Dig0 m)"
    and Dig1: "\<And>m. P m \<Longrightarrow> P (Dig1 m)"
  obtain n where "0 < n" and m: "m = num_of_nat n"
    by (cases m) auto
  from `0 < n` have "P (num_of_nat n)" proof (induct n rule: num_induct_raw)
    case 1 from `0 < n` show ?case .
  next
    case 2 with 1 show ?case by (simp add: one_num_def)
  next
    case (3 n) then have "P (num_of_nat n)" by auto
    then have "P (Dig0 (num_of_nat n))" by (rule Dig0)
    with 3 show ?case by (simp add: Dig0_def plus_num_def num_of_nat_inverse)
  next
    case (4 n) then have "P (num_of_nat n)" by auto
    then have "P (Dig1 (num_of_nat n))" by (rule Dig1)
    with 4 show ?case by (simp add: Dig1_def one_num_def plus_num_def num_of_nat_inverse)
  qed
  with m show "P m" by simp
next
  fix m n
  show "Dig0 m = Dig0 n \<longleftrightarrow> m = n"
    apply (cases m) apply (cases n)
    by (auto simp add: Dig0_def plus_num_def num_of_nat_inverse num_of_nat_inject)
next
  fix m n
  show "Dig1 m = Dig1 n \<longleftrightarrow> m = n"
    apply (cases m) apply (cases n)
    by (auto simp add: Dig1_def plus_num_def num_of_nat_inverse num_of_nat_inject)
next
  fix n
  show "1 \<noteq> Dig0 n"
    apply (cases n)
    by (auto simp add: Dig0_def one_num_def plus_num_def num_of_nat_inverse num_of_nat_inject)
next
  fix n
  show "1 \<noteq> Dig1 n"
    apply (cases n)
    by (auto simp add: Dig1_def one_num_def plus_num_def num_of_nat_inverse num_of_nat_inject)
next
  fix m n
  have "\<And>n m. n + n \<noteq> Suc (m + m)"
  proof -
    fix n m
    show "n + n \<noteq> Suc (m + m)"
    proof (induct m arbitrary: n)
      case 0 then show ?case by (cases n) simp_all
    next
      case (Suc m) then show ?case by (cases n) simp_all
    qed
  qed
  then show "Dig0 n \<noteq> Dig1 m"
    apply (cases n) apply (cases m)
    by (auto simp add: Dig0_def Dig1_def one_num_def plus_num_def num_of_nat_inverse num_of_nat_inject)
qed

text {*
  From now on, there are two possible models for @{typ num}:
  as positive naturals (rules @{text "num_induct"}, @{text "num_cases"})
  and as digit representation (rules @{text "num.induct"}, @{text "num.cases"}).

  It is not entirely clear in which context it is better to use
  the one or the other, or whether the construction should be reversed.
*}


subsection {* Binary numerals *}

text {*
  We embed binary representations into a generic algebraic
  structure using @{text of_num}
*}

ML {*
structure DigSimps =
  NamedThmsFun(val name = "numeral"; val description = "Simplification rules for numerals")
*}

setup DigSimps.setup

class semiring_numeral = semiring + monoid_mult
begin

primrec of_num :: "num \<Rightarrow> 'a" where
  of_num_one [numeral]: "of_num 1 = 1"
  | "of_num (Dig0 n) = of_num n + of_num n"
  | "of_num (Dig1 n) = of_num n + of_num n + 1"

declare of_num.simps [simp del]

end

text {*
  ML stuff and syntax.
*}

ML {*
fun mk_num 1 = @{term "1::num"}
  | mk_num k =
      let
        val (l, b) = Integer.div_mod k 2;
        val bit = (if b = 0 then @{term Dig0} else @{term Dig1});
      in bit $ (mk_num l) end;

fun dest_num @{term "1::num"} = 1
  | dest_num (@{term Dig0} $ n) = 2 * dest_num n
  | dest_num (@{term Dig1} $ n) = 2 * dest_num n + 1;

(*FIXME these have to gain proper context via morphisms phi*)

fun mk_numeral T k = Const (@{const_name of_num}, @{typ num} --> T)
  $ mk_num k

fun dest_numeral (Const (@{const_name of_num}, Type ("fun", [@{typ num}, T])) $ t) =
  (T, dest_num t)
*}

syntax
  "_Numerals" :: "xnum \<Rightarrow> 'a"    ("_")

parse_translation {*
let
  fun num_of_int n = if n > 0 then case IntInf.quotRem (n, 2)
     of (0, 1) => Const (@{const_name HOL.one}, dummyT)
      | (n, 0) => Const (@{const_name Dig0}, dummyT) $ num_of_int n
      | (n, 1) => Const (@{const_name Dig1}, dummyT) $ num_of_int n
    else raise Match;
  fun numeral_tr [Free (num, _)] =
        let
          val {leading_zeros, value, ...} = Syntax.read_xnum num;
          val _ = leading_zeros = 0 andalso value > 0
            orelse error ("Bad numeral: " ^ num);
        in Const (@{const_name of_num}, @{typ num} --> dummyT) $ num_of_int value end
    | numeral_tr ts = raise TERM ("numeral_tr", ts);
in [("_Numerals", numeral_tr)] end
*}

typed_print_translation {*
let
  fun dig b n = b + 2 * n; 
  fun int_of_num' (Const (@{const_syntax Dig0}, _) $ n) =
        dig 0 (int_of_num' n)
    | int_of_num' (Const (@{const_syntax Dig1}, _) $ n) =
        dig 1 (int_of_num' n)
    | int_of_num' (Const (@{const_syntax HOL.one}, _)) = 1;
  fun num_tr' show_sorts T [n] =
    let
      val k = int_of_num' n;
      val t' = Syntax.const "_Numerals" $ Syntax.free ("#" ^ string_of_int k);
    in case T
     of Type ("fun", [_, T']) =>
         if not (! show_types) andalso can Term.dest_Type T' then t'
         else Syntax.const Syntax.constrainC $ t' $ Syntax.term_of_typ show_sorts T'
      | T' => if T' = dummyT then t' else raise Match
    end;
in [(@{const_syntax of_num}, num_tr')] end
*}


subsection {* Numeral operations *}

text {*
  First, addition and multiplication on digits.
*}

lemma Dig_plus [numeral, simp, code]:
  "1 + 1 = Dig0 1"
  "1 + Dig0 m = Dig1 m"
  "1 + Dig1 m = Dig0 (m + 1)"
  "Dig0 n + 1 = Dig1 n"
  "Dig0 n + Dig0 m = Dig0 (n + m)"
  "Dig0 n + Dig1 m = Dig1 (n + m)"
  "Dig1 n + 1 = Dig0 (n + 1)"
  "Dig1 n + Dig0 m = Dig1 (n + m)"
  "Dig1 n + Dig1 m = Dig0 (n + m + 1)"
  by (simp_all add: add_ac Dig0_def Dig1_def)

lemma Dig_times [numeral, simp, code]:
  "1 * 1 = (1::num)"
  "1 * Dig0 n = Dig0 n"
  "1 * Dig1 n = Dig1 n"
  "Dig0 n * 1 = Dig0 n"
  "Dig0 n * Dig0 m = Dig0 (n * Dig0 m)"
  "Dig0 n * Dig1 m = Dig0 (n * Dig1 m)"
  "Dig1 n * 1 = Dig1 n"
  "Dig1 n * Dig0 m = Dig0 (n * Dig0 m + m)"
  "Dig1 n * Dig1 m = Dig1 (n * Dig1 m + m)"
  by (simp_all add: left_distrib right_distrib add_ac Dig0_def Dig1_def)

text {*
  @{const of_num} is a morphism.
*}

context semiring_numeral
begin

abbreviation "Num1 \<equiv> of_num 1"

text {*
  Alas, there is still the duplication of @{term 1},
  thought the duplicated @{term 0} has disappeared.
  We could get rid of it by replacing the constructor
  @{term 1} in @{typ num} by two constructors
  @{text two} and @{text three}, resulting in a further
  blow-up.  But it could be worth the effort.
*}

lemma of_num_plus_one [numeral]:
  "of_num n + 1 = of_num (n + 1)"
  by (rule sym, induct n) (simp_all add: Dig_plus of_num.simps add_ac)

lemma of_num_one_plus [numeral]:
  "1 + of_num n = of_num (n + 1)"
  unfolding of_num_plus_one [symmetric] add_commute ..

lemma of_num_plus [numeral]:
  "of_num m + of_num n = of_num (m + n)"
  by (induct n rule: num_induct)
    (simp_all add: Dig_plus of_num_one semigroup_add_class.add_assoc [symmetric, of m]
    add_ac of_num_plus_one [symmetric])

lemma of_num_times_one [numeral]:
  "of_num n * 1 = of_num n"
  by simp

lemma of_num_one_times [numeral]:
  "1 * of_num n = of_num n"
  by simp

lemma of_num_times [numeral]:
  "of_num m * of_num n = of_num (m * n)"
  by (induct n rule: num_induct)
    (simp_all add: of_num_plus [symmetric]
    semiring_class.right_distrib right_distrib of_num_one)

end

text {*
  Structures with a @{term 0}.
*}

context semiring_1
begin

subclass semiring_numeral ..

lemma of_nat_of_num [numeral]: "of_nat (of_num n) = of_num n"
  by (induct n)
    (simp_all add: semiring_numeral_class.of_num.simps of_num.simps add_ac)

declare of_nat_1 [numeral]

lemma Dig_plus_zero [numeral]:
  "0 + 1 = 1"
  "0 + of_num n = of_num n"
  "1 + 0 = 1"
  "of_num n + 0 = of_num n"
  by simp_all

lemma Dig_times_zero [numeral]:
  "0 * 1 = 0"
  "0 * of_num n = 0"
  "1 * 0 = 0"
  "of_num n * 0 = 0"
  by simp_all

end

lemma nat_of_num_of_num: "nat_of_num = of_num"
proof
  fix n
  have "of_num n = nat_of_num n" apply (induct n)
    apply (simp_all add: of_num.simps)
    using nat_of_num
    apply (simp_all add: one_num_def plus_num_def Dig0_def Dig1_def num_of_nat_inverse mem_def)
    done
  then show "nat_of_num n = of_num n" by simp
qed

text {*
  Equality.
*}

context semiring_char_0
begin

lemma of_num_eq_iff [numeral]:
  "of_num m = of_num n \<longleftrightarrow> m = n"
  unfolding of_nat_of_num [symmetric] nat_of_num_of_num [symmetric]
    of_nat_eq_iff nat_of_num_inject ..

lemma of_num_eq_one_iff [numeral]:
  "of_num n = 1 \<longleftrightarrow> n = 1"
proof -
  have "of_num n = of_num 1 \<longleftrightarrow> n = 1" unfolding of_num_eq_iff ..
  then show ?thesis by (simp add: of_num_one)
qed

lemma one_eq_of_num_iff [numeral]:
  "1 = of_num n \<longleftrightarrow> n = 1"
  unfolding of_num_eq_one_iff [symmetric] by auto

end

text {*
  Comparisons.  Could be perhaps more general than here.
*}

lemma (in ordered_semidom) of_num_pos: "0 < of_num n"
proof -
  have "(0::nat) < of_num n"
    by (induct n) (simp_all add: semiring_numeral_class.of_num.simps)
  then have "of_nat 0 \<noteq> of_nat (of_num n)" 
    by (cases n) (simp_all only: semiring_numeral_class.of_num.simps of_nat_eq_iff)
  then have "0 \<noteq> of_num n"
    by (simp add: of_nat_of_num)
  moreover have "0 \<le> of_nat (of_num n)" by simp
  ultimately show ?thesis by (simp add: of_nat_of_num)
qed

instantiation num :: linorder
begin

definition less_eq_num :: "num \<Rightarrow> num \<Rightarrow> bool" where
  [code del]: "m \<le> n \<longleftrightarrow> nat_of_num m \<le> nat_of_num n"

definition less_num :: "num \<Rightarrow> num \<Rightarrow> bool" where
  [code del]: "m < n \<longleftrightarrow> nat_of_num m < nat_of_num n"

instance proof
qed (auto simp add: less_eq_num_def less_num_def
  split_num_all num_of_nat_inverse num_of_nat_inject split: split_if_asm)

end

lemma less_eq_num_code [numeral, simp, code]:
  "(1::num) \<le> n \<longleftrightarrow> True"
  "Dig0 m \<le> 1 \<longleftrightarrow> False"
  "Dig1 m \<le> 1 \<longleftrightarrow> False"
  "Dig0 m \<le> Dig0 n \<longleftrightarrow> m \<le> n"
  "Dig0 m \<le> Dig1 n \<longleftrightarrow> m \<le> n"
  "Dig1 m \<le> Dig1 n \<longleftrightarrow> m \<le> n"
  "Dig1 m \<le> Dig0 n \<longleftrightarrow> m < n"
  using of_num_pos [of n, where ?'a = nat] of_num_pos [of m, where ?'a = nat]
  by (auto simp add: less_eq_num_def less_num_def nat_of_num_of_num of_num.simps)

lemma less_num_code [numeral, simp, code]:
  "m < (1::num) \<longleftrightarrow> False"
  "(1::num) < 1 \<longleftrightarrow> False"
  "1 < Dig0 n \<longleftrightarrow> True"
  "1 < Dig1 n \<longleftrightarrow> True"
  "Dig0 m < Dig0 n \<longleftrightarrow> m < n"
  "Dig0 m < Dig1 n \<longleftrightarrow> m \<le> n"
  "Dig1 m < Dig1 n \<longleftrightarrow> m < n"
  "Dig1 m < Dig0 n \<longleftrightarrow> m < n"
  using of_num_pos [of n, where ?'a = nat] of_num_pos [of m, where ?'a = nat]
  by (auto simp add: less_eq_num_def less_num_def nat_of_num_of_num of_num.simps)
  
context ordered_semidom
begin

lemma of_num_less_eq_iff [numeral]: "of_num m \<le> of_num n \<longleftrightarrow> m \<le> n"
proof -
  have "of_nat (of_num m) \<le> of_nat (of_num n) \<longleftrightarrow> m \<le> n"
    unfolding less_eq_num_def nat_of_num_of_num of_nat_le_iff ..
  then show ?thesis by (simp add: of_nat_of_num)
qed

lemma of_num_less_eq_one_iff [numeral]: "of_num n \<le> 1 \<longleftrightarrow> n = 1"
proof -
  have "of_num n \<le> of_num 1 \<longleftrightarrow> n = 1"
    by (cases n) (simp_all add: of_num_less_eq_iff)
  then show ?thesis by (simp add: of_num_one)
qed

lemma one_less_eq_of_num_iff [numeral]: "1 \<le> of_num n"
proof -
  have "of_num 1 \<le> of_num n"
    by (cases n) (simp_all add: of_num_less_eq_iff)
  then show ?thesis by (simp add: of_num_one)
qed

lemma of_num_less_iff [numeral]: "of_num m < of_num n \<longleftrightarrow> m < n"
proof -
  have "of_nat (of_num m) < of_nat (of_num n) \<longleftrightarrow> m < n"
    unfolding less_num_def nat_of_num_of_num of_nat_less_iff ..
  then show ?thesis by (simp add: of_nat_of_num)
qed

lemma of_num_less_one_iff [numeral]: "\<not> of_num n < 1"
proof -
  have "\<not> of_num n < of_num 1"
    by (cases n) (simp_all add: of_num_less_iff)
  then show ?thesis by (simp add: of_num_one)
qed

lemma one_less_of_num_iff [numeral]: "1 < of_num n \<longleftrightarrow> n \<noteq> 1"
proof -
  have "of_num 1 < of_num n \<longleftrightarrow> n \<noteq> 1"
    by (cases n) (simp_all add: of_num_less_iff)
  then show ?thesis by (simp add: of_num_one)
qed

end

text {*
  Structures with subtraction @{term "op -"}.
*}

text {* A double-and-decrement function *}

primrec DigM :: "num \<Rightarrow> num" where
  "DigM 1 = 1"
  | "DigM (Dig0 n) = Dig1 (DigM n)"
  | "DigM (Dig1 n) = Dig1 (Dig0 n)"

lemma DigM_plus_one: "DigM n + 1 = Dig0 n"
  by (induct n) simp_all

lemma one_plus_DigM: "1 + DigM n = Dig0 n"
  unfolding add_commute [of 1] DigM_plus_one ..

class semiring_minus = semiring + minus + zero +
  assumes minus_inverts_plus1: "a + b = c \<Longrightarrow> c - b = a"
  assumes minus_minus_zero_inverts_plus1: "a + b = c \<Longrightarrow> b - c = 0 - a"
begin

lemma minus_inverts_plus2: "a + b = c \<Longrightarrow> c - a = b"
  by (simp add: add_ac minus_inverts_plus1 [of b a])

lemma minus_minus_zero_inverts_plus2: "a + b = c \<Longrightarrow> a - c = 0 - b"
  by (simp add: add_ac minus_minus_zero_inverts_plus1 [of b a])

end

class semiring_1_minus = semiring_1 + semiring_minus
begin

lemma Dig_of_num_pos:
  assumes "k + n = m"
  shows "of_num m - of_num n = of_num k"
  using assms by (simp add: of_num_plus minus_inverts_plus1)

lemma Dig_of_num_zero:
  shows "of_num n - of_num n = 0"
  by (rule minus_inverts_plus1) simp

lemma Dig_of_num_neg:
  assumes "k + m = n"
  shows "of_num m - of_num n = 0 - of_num k"
  by (rule minus_minus_zero_inverts_plus1) (simp add: of_num_plus assms)

lemmas Dig_plus_eval =
  of_num_plus of_num_eq_iff Dig_plus refl [of "1::num", THEN eqTrueI] num.inject

simproc_setup numeral_minus ("of_num m - of_num n") = {*
  let
    (*TODO proper implicit use of morphism via pattern antiquotations*)
    fun cdest_of_num ct = (snd o split_last o snd o Drule.strip_comb) ct;
    fun cdest_minus ct = case (rev o snd o Drule.strip_comb) ct of [n, m] => (m, n);
    fun attach_num ct = (dest_num (Thm.term_of ct), ct);
    fun cdifference t = (pairself (attach_num o cdest_of_num) o cdest_minus) t;
    val simplify = MetaSimplifier.rewrite false (map mk_meta_eq @{thms Dig_plus_eval});
    fun cert ck cl cj = @{thm eqTrueE} OF [@{thm meta_eq_to_obj_eq} OF [simplify (Drule.list_comb (@{cterm "op = :: num \<Rightarrow> _"},
      [Drule.list_comb (@{cterm "op + :: num \<Rightarrow> _"}, [ck, cl]), cj]))]];
  in fn phi => fn _ => fn ct => case try cdifference ct
   of NONE => (NONE)
    | SOME ((k, ck), (l, cl)) => SOME (let val j = k - l in if j = 0
        then MetaSimplifier.rewrite false [mk_meta_eq (Morphism.thm phi @{thm Dig_of_num_zero})] ct
        else mk_meta_eq (let
          val cj = Thm.cterm_of (Thm.theory_of_cterm ct) (mk_num (abs j));
        in
          (if j > 0 then (Morphism.thm phi @{thm Dig_of_num_pos}) OF [cert cj cl ck]
          else (Morphism.thm phi @{thm Dig_of_num_neg}) OF [cert cj ck cl])
        end) end)
  end
*}

lemma Dig_of_num_minus_zero [numeral]:
  "of_num n - 0 = of_num n"
  by (simp add: minus_inverts_plus1)

lemma Dig_one_minus_zero [numeral]:
  "1 - 0 = 1"
  by (simp add: minus_inverts_plus1)

lemma Dig_one_minus_one [numeral]:
  "1 - 1 = 0"
  by (simp add: minus_inverts_plus1)

lemma Dig_of_num_minus_one [numeral]:
  "of_num (Dig0 n) - 1 = of_num (DigM n)"
  "of_num (Dig1 n) - 1 = of_num (Dig0 n)"
  by (auto intro: minus_inverts_plus1 simp add: DigM_plus_one of_num.simps of_num_plus_one)

lemma Dig_one_minus_of_num [numeral]:
  "1 - of_num (Dig0 n) = 0 - of_num (DigM n)"
  "1 - of_num (Dig1 n) = 0 - of_num (Dig0 n)"
  by (auto intro: minus_minus_zero_inverts_plus1 simp add: DigM_plus_one of_num.simps of_num_plus_one)

end

context ring_1
begin

subclass semiring_1_minus
  proof qed (simp_all add: algebra_simps)

lemma Dig_zero_minus_of_num [numeral]:
  "0 - of_num n = - of_num n"
  by simp

lemma Dig_zero_minus_one [numeral]:
  "0 - 1 = - 1"
  by simp

lemma Dig_uminus_uminus [numeral]:
  "- (- of_num n) = of_num n"
  by simp

lemma Dig_plus_uminus [numeral]:
  "of_num m + - of_num n = of_num m - of_num n"
  "- of_num m + of_num n = of_num n - of_num m"
  "- of_num m + - of_num n = - (of_num m + of_num n)"
  "of_num m - - of_num n = of_num m + of_num n"
  "- of_num m - of_num n = - (of_num m + of_num n)"
  "- of_num m - - of_num n = of_num n - of_num m"
  by (simp_all add: diff_minus add_commute)

lemma Dig_times_uminus [numeral]:
  "- of_num n * of_num m = - (of_num n * of_num m)"
  "of_num n * - of_num m = - (of_num n * of_num m)"
  "- of_num n * - of_num m = of_num n * of_num m"
  by (simp_all add: minus_mult_left [symmetric] minus_mult_right [symmetric])

lemma of_int_of_num [numeral]: "of_int (of_num n) = of_num n"
by (induct n)
  (simp_all only: of_num.simps semiring_numeral_class.of_num.simps of_int_add, simp_all)

declare of_int_1 [numeral]

end

text {*
  Greetings to @{typ nat}.
*}

instance nat :: semiring_1_minus proof qed simp_all

lemma Suc_of_num [numeral]: "Suc (of_num n) = of_num (n + 1)"
  unfolding of_num_plus_one [symmetric] by simp

lemma nat_number:
  "1 = Suc 0"
  "of_num 1 = Suc 0"
  "of_num (Dig0 n) = Suc (of_num (DigM n))"
  "of_num (Dig1 n) = Suc (of_num (Dig0 n))"
  by (simp_all add: of_num.simps DigM_plus_one Suc_of_num)

declare diff_0_eq_0 [numeral]


subsection {* Code generator setup for @{typ int} *}

definition Pls :: "num \<Rightarrow> int" where
  [simp, code post]: "Pls n = of_num n"

definition Mns :: "num \<Rightarrow> int" where
  [simp, code post]: "Mns n = - of_num n"

code_datatype "0::int" Pls Mns

lemmas [code inline] = Pls_def [symmetric] Mns_def [symmetric]

definition sub :: "num \<Rightarrow> num \<Rightarrow> int" where
  [simp, code del]: "sub m n = (of_num m - of_num n)"

definition dup :: "int \<Rightarrow> int" where
  [code del]: "dup k = 2 * k"

lemma Dig_sub [code]:
  "sub 1 1 = 0"
  "sub (Dig0 m) 1 = of_num (DigM m)"
  "sub (Dig1 m) 1 = of_num (Dig0 m)"
  "sub 1 (Dig0 n) = - of_num (DigM n)"
  "sub 1 (Dig1 n) = - of_num (Dig0 n)"
  "sub (Dig0 m) (Dig0 n) = dup (sub m n)"
  "sub (Dig1 m) (Dig1 n) = dup (sub m n)"
  "sub (Dig1 m) (Dig0 n) = dup (sub m n) + 1"
  "sub (Dig0 m) (Dig1 n) = dup (sub m n) - 1"
  apply (simp_all add: dup_def algebra_simps)
  apply (simp_all add: of_num_plus one_plus_DigM)[4]
  apply (simp_all add: of_num.simps)
  done

lemma dup_code [code]:
  "dup 0 = 0"
  "dup (Pls n) = Pls (Dig0 n)"
  "dup (Mns n) = Mns (Dig0 n)"
  by (simp_all add: dup_def of_num.simps)
  
lemma [code, code del]:
  "(1 :: int) = 1"
  "(op + :: int \<Rightarrow> int \<Rightarrow> int) = op +"
  "(uminus :: int \<Rightarrow> int) = uminus"
  "(op - :: int \<Rightarrow> int \<Rightarrow> int) = op -"
  "(op * :: int \<Rightarrow> int \<Rightarrow> int) = op *"
  "(eq_class.eq :: int \<Rightarrow> int \<Rightarrow> bool) = eq_class.eq"
  "(op \<le> :: int \<Rightarrow> int \<Rightarrow> bool) = op \<le>"
  "(op < :: int \<Rightarrow> int \<Rightarrow> bool) = op <"
  by rule+

lemma one_int_code [code]:
  "1 = Pls 1"
  by (simp add: of_num_one)

lemma plus_int_code [code]:
  "k + 0 = (k::int)"
  "0 + l = (l::int)"
  "Pls m + Pls n = Pls (m + n)"
  "Pls m - Pls n = sub m n"
  "Mns m + Mns n = Mns (m + n)"
  "Mns m - Mns n = sub n m"
  by (simp_all add: of_num_plus [symmetric])

lemma uminus_int_code [code]:
  "uminus 0 = (0::int)"
  "uminus (Pls m) = Mns m"
  "uminus (Mns m) = Pls m"
  by simp_all

lemma minus_int_code [code]:
  "k - 0 = (k::int)"
  "0 - l = uminus (l::int)"
  "Pls m - Pls n = sub m n"
  "Pls m - Mns n = Pls (m + n)"
  "Mns m - Pls n = Mns (m + n)"
  "Mns m - Mns n = sub n m"
  by (simp_all add: of_num_plus [symmetric])

lemma times_int_code [code]:
  "k * 0 = (0::int)"
  "0 * l = (0::int)"
  "Pls m * Pls n = Pls (m * n)"
  "Pls m * Mns n = Mns (m * n)"
  "Mns m * Pls n = Mns (m * n)"
  "Mns m * Mns n = Pls (m * n)"
  by (simp_all add: of_num_times [symmetric])

lemma eq_int_code [code]:
  "eq_class.eq 0 (0::int) \<longleftrightarrow> True"
  "eq_class.eq 0 (Pls l) \<longleftrightarrow> False"
  "eq_class.eq 0 (Mns l) \<longleftrightarrow> False"
  "eq_class.eq (Pls k) 0 \<longleftrightarrow> False"
  "eq_class.eq (Pls k) (Pls l) \<longleftrightarrow> eq_class.eq k l"
  "eq_class.eq (Pls k) (Mns l) \<longleftrightarrow> False"
  "eq_class.eq (Mns k) 0 \<longleftrightarrow> False"
  "eq_class.eq (Mns k) (Pls l) \<longleftrightarrow> False"
  "eq_class.eq (Mns k) (Mns l) \<longleftrightarrow> eq_class.eq k l"
  using of_num_pos [of l, where ?'a = int] of_num_pos [of k, where ?'a = int]
  by (simp_all add: of_num_eq_iff eq)

lemma less_eq_int_code [code]:
  "0 \<le> (0::int) \<longleftrightarrow> True"
  "0 \<le> Pls l \<longleftrightarrow> True"
  "0 \<le> Mns l \<longleftrightarrow> False"
  "Pls k \<le> 0 \<longleftrightarrow> False"
  "Pls k \<le> Pls l \<longleftrightarrow> k \<le> l"
  "Pls k \<le> Mns l \<longleftrightarrow> False"
  "Mns k \<le> 0 \<longleftrightarrow> True"
  "Mns k \<le> Pls l \<longleftrightarrow> True"
  "Mns k \<le> Mns l \<longleftrightarrow> l \<le> k"
  using of_num_pos [of l, where ?'a = int] of_num_pos [of k, where ?'a = int]
  by (simp_all add: of_num_less_eq_iff)

lemma less_int_code [code]:
  "0 < (0::int) \<longleftrightarrow> False"
  "0 < Pls l \<longleftrightarrow> True"
  "0 < Mns l \<longleftrightarrow> False"
  "Pls k < 0 \<longleftrightarrow> False"
  "Pls k < Pls l \<longleftrightarrow> k < l"
  "Pls k < Mns l \<longleftrightarrow> False"
  "Mns k < 0 \<longleftrightarrow> True"
  "Mns k < Pls l \<longleftrightarrow> True"
  "Mns k < Mns l \<longleftrightarrow> l < k"
  using of_num_pos [of l, where ?'a = int] of_num_pos [of k, where ?'a = int]
  by (simp_all add: of_num_less_iff)

lemma [code inline del]: "(0::int) \<equiv> Numeral0" by simp
lemma [code inline del]: "(1::int) \<equiv> Numeral1" by simp
declare zero_is_num_zero [code inline del]
declare one_is_num_one [code inline del]

hide (open) const sub dup


subsection {* Numeral equations as default simplification rules *}

text {* TODO.  Be more precise here with respect to subsumed facts. *}
declare (in semiring_numeral) numeral [simp]
declare (in semiring_1) numeral [simp]
declare (in semiring_char_0) numeral [simp]
declare (in ring_1) numeral [simp]
thm numeral


text {* Toy examples *}

definition "bar \<longleftrightarrow> #4 * #2 + #7 = (#8 :: nat) \<and> #4 * #2 + #7 \<ge> (#8 :: int) - #3"
code_thms bar
export_code bar in Haskell file -
export_code bar in OCaml module_name Foo file -
ML {* @{code bar} *}

end
