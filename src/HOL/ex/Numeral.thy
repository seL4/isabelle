(*  Title:      HOL/ex/Numeral.thy
    Author:     Florian Haftmann
*)

header {* An experimental alternative numeral representation. *}

theory Numeral
imports Main
begin

subsection {* The @{text num} type *}

datatype num = One | Dig0 num | Dig1 num

text {* Increment function for type @{typ num} *}

primrec inc :: "num \<Rightarrow> num" where
  "inc One = Dig0 One"
| "inc (Dig0 x) = Dig1 x"
| "inc (Dig1 x) = Dig0 (inc x)"

text {* Converting between type @{typ num} and type @{typ nat} *}

primrec nat_of_num :: "num \<Rightarrow> nat" where
  "nat_of_num One = Suc 0"
| "nat_of_num (Dig0 x) = nat_of_num x + nat_of_num x"
| "nat_of_num (Dig1 x) = Suc (nat_of_num x + nat_of_num x)"

primrec num_of_nat :: "nat \<Rightarrow> num" where
  "num_of_nat 0 = One"
| "num_of_nat (Suc n) = (if 0 < n then inc (num_of_nat n) else One)"

lemma nat_of_num_pos: "0 < nat_of_num x"
  by (induct x) simp_all

lemma nat_of_num_neq_0: "nat_of_num x \<noteq> 0"
  by (induct x) simp_all

lemma nat_of_num_inc: "nat_of_num (inc x) = Suc (nat_of_num x)"
  by (induct x) simp_all

lemma num_of_nat_double:
  "0 < n \<Longrightarrow> num_of_nat (n + n) = Dig0 (num_of_nat n)"
  by (induct n) simp_all

text {*
  Type @{typ num} is isomorphic to the strictly positive
  natural numbers.
*}

lemma nat_of_num_inverse: "num_of_nat (nat_of_num x) = x"
  by (induct x) (simp_all add: num_of_nat_double nat_of_num_pos)

lemma num_of_nat_inverse: "0 < n \<Longrightarrow> nat_of_num (num_of_nat n) = n"
  by (induct n) (simp_all add: nat_of_num_inc)

lemma num_eq_iff: "x = y \<longleftrightarrow> nat_of_num x = nat_of_num y"
proof
  assume "nat_of_num x = nat_of_num y"
  then have "num_of_nat (nat_of_num x) = num_of_nat (nat_of_num y)" by simp
  then show "x = y" by (simp add: nat_of_num_inverse)
qed simp

lemma num_induct [case_names One inc]:
  fixes P :: "num \<Rightarrow> bool"
  assumes One: "P One"
    and inc: "\<And>x. P x \<Longrightarrow> P (inc x)"
  shows "P x"
proof -
  obtain n where n: "Suc n = nat_of_num x"
    by (cases "nat_of_num x", simp_all add: nat_of_num_neq_0)
  have "P (num_of_nat (Suc n))"
  proof (induct n)
    case 0 show ?case using One by simp
  next
    case (Suc n)
    then have "P (inc (num_of_nat (Suc n)))" by (rule inc)
    then show "P (num_of_nat (Suc (Suc n)))" by simp
  qed
  with n show "P x"
    by (simp add: nat_of_num_inverse)
qed

text {*
  From now on, there are two possible models for @{typ num}: as
  positive naturals (rule @{text "num_induct"}) and as digit
  representation (rules @{text "num.induct"}, @{text "num.cases"}).

  It is not entirely clear in which context it is better to use the
  one or the other, or whether the construction should be reversed.
*}


subsection {* Numeral operations *}

ML {*
structure Dig_Simps = Named_Thms
(
  val name = @{binding numeral}
  val description = "simplification rules for numerals"
)
*}

setup Dig_Simps.setup

instantiation num :: "{plus,times,ord}"
begin

definition plus_num :: "num \<Rightarrow> num \<Rightarrow> num" where
  "m + n = num_of_nat (nat_of_num m + nat_of_num n)"

definition times_num :: "num \<Rightarrow> num \<Rightarrow> num" where
  "m * n = num_of_nat (nat_of_num m * nat_of_num n)"

definition less_eq_num :: "num \<Rightarrow> num \<Rightarrow> bool" where
  "m \<le> n \<longleftrightarrow> nat_of_num m \<le> nat_of_num n"

definition less_num :: "num \<Rightarrow> num \<Rightarrow> bool" where
  "m < n \<longleftrightarrow> nat_of_num m < nat_of_num n"

instance ..

end

lemma nat_of_num_add: "nat_of_num (x + y) = nat_of_num x + nat_of_num y"
  unfolding plus_num_def
  by (intro num_of_nat_inverse add_pos_pos nat_of_num_pos)

lemma nat_of_num_mult: "nat_of_num (x * y) = nat_of_num x * nat_of_num y"
  unfolding times_num_def
  by (intro num_of_nat_inverse mult_pos_pos nat_of_num_pos)

lemma Dig_plus [numeral, simp, code]:
  "One + One = Dig0 One"
  "One + Dig0 m = Dig1 m"
  "One + Dig1 m = Dig0 (m + One)"
  "Dig0 n + One = Dig1 n"
  "Dig0 n + Dig0 m = Dig0 (n + m)"
  "Dig0 n + Dig1 m = Dig1 (n + m)"
  "Dig1 n + One = Dig0 (n + One)"
  "Dig1 n + Dig0 m = Dig1 (n + m)"
  "Dig1 n + Dig1 m = Dig0 (n + m + One)"
  by (simp_all add: num_eq_iff nat_of_num_add)

lemma Dig_times [numeral, simp, code]:
  "One * One = One"
  "One * Dig0 n = Dig0 n"
  "One * Dig1 n = Dig1 n"
  "Dig0 n * One = Dig0 n"
  "Dig0 n * Dig0 m = Dig0 (n * Dig0 m)"
  "Dig0 n * Dig1 m = Dig0 (n * Dig1 m)"
  "Dig1 n * One = Dig1 n"
  "Dig1 n * Dig0 m = Dig0 (n * Dig0 m + m)"
  "Dig1 n * Dig1 m = Dig1 (n * Dig1 m + m)"
  by (simp_all add: num_eq_iff nat_of_num_add nat_of_num_mult
                    left_distrib right_distrib)

lemma less_eq_num_code [numeral, simp, code]:
  "One \<le> n \<longleftrightarrow> True"
  "Dig0 m \<le> One \<longleftrightarrow> False"
  "Dig1 m \<le> One \<longleftrightarrow> False"
  "Dig0 m \<le> Dig0 n \<longleftrightarrow> m \<le> n"
  "Dig0 m \<le> Dig1 n \<longleftrightarrow> m \<le> n"
  "Dig1 m \<le> Dig1 n \<longleftrightarrow> m \<le> n"
  "Dig1 m \<le> Dig0 n \<longleftrightarrow> m < n"
  using nat_of_num_pos [of n] nat_of_num_pos [of m]
  by (auto simp add: less_eq_num_def less_num_def)

lemma less_num_code [numeral, simp, code]:
  "m < One \<longleftrightarrow> False"
  "One < One \<longleftrightarrow> False"
  "One < Dig0 n \<longleftrightarrow> True"
  "One < Dig1 n \<longleftrightarrow> True"
  "Dig0 m < Dig0 n \<longleftrightarrow> m < n"
  "Dig0 m < Dig1 n \<longleftrightarrow> m \<le> n"
  "Dig1 m < Dig1 n \<longleftrightarrow> m < n"
  "Dig1 m < Dig0 n \<longleftrightarrow> m < n"
  using nat_of_num_pos [of n] nat_of_num_pos [of m]
  by (auto simp add: less_eq_num_def less_num_def)

text {* Rules using @{text One} and @{text inc} as constructors *}

lemma add_One: "x + One = inc x"
  by (simp add: num_eq_iff nat_of_num_add nat_of_num_inc)

lemma add_inc: "x + inc y = inc (x + y)"
  by (simp add: num_eq_iff nat_of_num_add nat_of_num_inc)

lemma mult_One: "x * One = x"
  by (simp add: num_eq_iff nat_of_num_mult)

lemma mult_inc: "x * inc y = x * y + x"
  by (simp add: num_eq_iff nat_of_num_mult nat_of_num_add nat_of_num_inc)

text {* A double-and-decrement function *}

primrec DigM :: "num \<Rightarrow> num" where
  "DigM One = One"
| "DigM (Dig0 n) = Dig1 (DigM n)"
| "DigM (Dig1 n) = Dig1 (Dig0 n)"

lemma DigM_plus_one: "DigM n + One = Dig0 n"
  by (induct n) simp_all

lemma add_One_commute: "One + n = n + One"
  by (induct n) simp_all

lemma one_plus_DigM: "One + DigM n = Dig0 n"
  by (simp add: add_One_commute DigM_plus_one)

text {* Squaring and exponentiation *}

primrec square :: "num \<Rightarrow> num" where
  "square One = One"
| "square (Dig0 n) = Dig0 (Dig0 (square n))"
| "square (Dig1 n) = Dig1 (Dig0 (square n + n))"

primrec pow :: "num \<Rightarrow> num \<Rightarrow> num" where
  "pow x One = x"
| "pow x (Dig0 y) = square (pow x y)"
| "pow x (Dig1 y) = x * square (pow x y)"


subsection {* Binary numerals *}

text {*
  We embed binary representations into a generic algebraic
  structure using @{text of_num}.
*}

class semiring_numeral = semiring + monoid_mult
begin

primrec of_num :: "num \<Rightarrow> 'a" where
  of_num_One [numeral]: "of_num One = 1"
| "of_num (Dig0 n) = of_num n + of_num n"
| "of_num (Dig1 n) = of_num n + of_num n + 1"

lemma of_num_inc: "of_num (inc n) = of_num n + 1"
  by (induct n) (simp_all add: add_ac)

lemma of_num_add: "of_num (m + n) = of_num m + of_num n"
  by (induct n rule: num_induct) (simp_all add: add_One add_inc of_num_inc add_ac)

lemma of_num_mult: "of_num (m * n) = of_num m * of_num n"
  by (induct n rule: num_induct) (simp_all add: mult_One mult_inc of_num_add of_num_inc right_distrib)

declare of_num.simps [simp del]

end

ML {*
fun mk_num k =
  if k > 1 then
    let
      val (l, b) = Integer.div_mod k 2;
      val bit = (if b = 0 then @{term Dig0} else @{term Dig1});
    in bit $ (mk_num l) end
  else if k = 1 then @{term One}
  else error ("mk_num " ^ string_of_int k);

fun dest_num @{term One} = 1
  | dest_num (@{term Dig0} $ n) = 2 * dest_num n
  | dest_num (@{term Dig1} $ n) = 2 * dest_num n + 1
  | dest_num t = raise TERM ("dest_num", [t]);

fun mk_numeral phi T k = Morphism.term phi (Const (@{const_name of_num}, @{typ num} --> T))
  $ mk_num k

fun dest_numeral phi (u $ t) =
  if Term.aconv_untyped (u, Morphism.term phi (Const (@{const_name of_num}, dummyT)))
  then (range_type (fastype_of u), dest_num t)
  else raise TERM ("dest_numeral", [u, t]);
*}

syntax
  "_Numerals" :: "xnum_token \<Rightarrow> 'a"    ("_")

parse_translation {*
let
  fun num_of_int n = if n > 0 then case IntInf.quotRem (n, 2)
     of (0, 1) => Const (@{const_name One}, dummyT)
      | (n, 0) => Const (@{const_name Dig0}, dummyT) $ num_of_int n
      | (n, 1) => Const (@{const_name Dig1}, dummyT) $ num_of_int n
    else raise Match;
  fun numeral_tr [Free (num, _)] =
        let
          val {leading_zeros, value, ...} = Lexicon.read_xnum num;
          val _ = leading_zeros = 0 andalso value > 0
            orelse error ("Bad numeral: " ^ num);
        in Const (@{const_name of_num}, @{typ num} --> dummyT) $ num_of_int value end
    | numeral_tr ts = raise TERM ("numeral_tr", ts);
in [(@{syntax_const "_Numerals"}, numeral_tr)] end
*}

typed_print_translation (advanced) {*
let
  fun dig b n = b + 2 * n; 
  fun int_of_num' (Const (@{const_syntax Dig0}, _) $ n) =
        dig 0 (int_of_num' n)
    | int_of_num' (Const (@{const_syntax Dig1}, _) $ n) =
        dig 1 (int_of_num' n)
    | int_of_num' (Const (@{const_syntax One}, _)) = 1;
  fun num_tr' ctxt T [n] =
    let
      val k = int_of_num' n;
      val t' = Syntax.const @{syntax_const "_Numerals"} $ Syntax.free ("#" ^ string_of_int k);
    in
      case T of
        Type (@{type_name fun}, [_, T']) =>
          if not (Config.get ctxt show_types) andalso can Term.dest_Type T' then t'
          else Syntax.const @{syntax_const "_constrain"} $ t' $ Syntax_Phases.term_of_typ ctxt T'
      | T' => if T' = dummyT then t' else raise Match
    end;
in [(@{const_syntax of_num}, num_tr')] end
*}


subsection {* Class-specific numeral rules *}

subsubsection {* Class @{text semiring_numeral} *}

context semiring_numeral
begin

abbreviation "Num1 \<equiv> of_num One"

text {*
  Alas, there is still the duplication of @{term 1}, although the
  duplicated @{term 0} has disappeared.  We could get rid of it by
  replacing the constructor @{term 1} in @{typ num} by two
  constructors @{text two} and @{text three}, resulting in a further
  blow-up.  But it could be worth the effort.
*}

lemma of_num_plus_one [numeral]:
  "of_num n + 1 = of_num (n + One)"
  by (simp only: of_num_add of_num_One)

lemma of_num_one_plus [numeral]:
  "1 + of_num n = of_num (One + n)"
  by (simp only: of_num_add of_num_One)

lemma of_num_plus [numeral]:
  "of_num m + of_num n = of_num (m + n)"
  by (simp only: of_num_add)

lemma of_num_times_one [numeral]:
  "of_num n * 1 = of_num n"
  by simp

lemma of_num_one_times [numeral]:
  "1 * of_num n = of_num n"
  by simp

lemma of_num_times [numeral]:
  "of_num m * of_num n = of_num (m * n)"
  unfolding of_num_mult ..

end


subsubsection {* Structures with a zero: class @{text semiring_1} *}

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
  have "of_num n = nat_of_num n"
    by (induct n) (simp_all add: of_num.simps)
  then show "nat_of_num n = of_num n" by simp
qed


subsubsection {* Equality: class @{text semiring_char_0} *}

context semiring_char_0
begin

lemma of_num_eq_iff [numeral]: "of_num m = of_num n \<longleftrightarrow> m = n"
  unfolding of_nat_of_num [symmetric] nat_of_num_of_num [symmetric]
    of_nat_eq_iff num_eq_iff ..

lemma of_num_eq_one_iff [numeral]: "of_num n = 1 \<longleftrightarrow> n = One"
  using of_num_eq_iff [of n One] by (simp add: of_num_One)

lemma one_eq_of_num_iff [numeral]: "1 = of_num n \<longleftrightarrow> One = n"
  using of_num_eq_iff [of One n] by (simp add: of_num_One)

end


subsubsection {* Comparisons: class @{text linordered_semidom} *}

text {*
  Perhaps the underlying structure could even 
  be more general than @{text linordered_semidom}.
*}

context linordered_semidom
begin

lemma of_num_pos [numeral]: "0 < of_num n"
  by (induct n) (simp_all add: of_num.simps add_pos_pos)

lemma of_num_not_zero [numeral]: "of_num n \<noteq> 0"
  using of_num_pos [of n] by simp

lemma of_num_less_eq_iff [numeral]: "of_num m \<le> of_num n \<longleftrightarrow> m \<le> n"
proof -
  have "of_nat (of_num m) \<le> of_nat (of_num n) \<longleftrightarrow> m \<le> n"
    unfolding less_eq_num_def nat_of_num_of_num of_nat_le_iff ..
  then show ?thesis by (simp add: of_nat_of_num)
qed

lemma of_num_less_eq_one_iff [numeral]: "of_num n \<le> 1 \<longleftrightarrow> n \<le> One"
  using of_num_less_eq_iff [of n One] by (simp add: of_num_One)

lemma one_less_eq_of_num_iff [numeral]: "1 \<le> of_num n"
  using of_num_less_eq_iff [of One n] by (simp add: of_num_One)

lemma of_num_less_iff [numeral]: "of_num m < of_num n \<longleftrightarrow> m < n"
proof -
  have "of_nat (of_num m) < of_nat (of_num n) \<longleftrightarrow> m < n"
    unfolding less_num_def nat_of_num_of_num of_nat_less_iff ..
  then show ?thesis by (simp add: of_nat_of_num)
qed

lemma of_num_less_one_iff [numeral]: "\<not> of_num n < 1"
  using of_num_less_iff [of n One] by (simp add: of_num_One)

lemma one_less_of_num_iff [numeral]: "1 < of_num n \<longleftrightarrow> One < n"
  using of_num_less_iff [of One n] by (simp add: of_num_One)

lemma of_num_nonneg [numeral]: "0 \<le> of_num n"
  by (induct n) (simp_all add: of_num.simps add_nonneg_nonneg)

lemma of_num_less_zero_iff [numeral]: "\<not> of_num n < 0"
  by (simp add: not_less of_num_nonneg)

lemma of_num_le_zero_iff [numeral]: "\<not> of_num n \<le> 0"
  by (simp add: not_le of_num_pos)

end

context linordered_idom
begin

lemma minus_of_num_less_of_num_iff: "- of_num m < of_num n"
proof -
  have "- of_num m < 0" by (simp add: of_num_pos)
  also have "0 < of_num n" by (simp add: of_num_pos)
  finally show ?thesis .
qed

lemma minus_of_num_not_equal_of_num: "- of_num m \<noteq> of_num n"
  using minus_of_num_less_of_num_iff [of m n] by simp

lemma minus_of_num_less_one_iff: "- of_num n < 1"
  using minus_of_num_less_of_num_iff [of n One] by (simp add: of_num_One)

lemma minus_one_less_of_num_iff: "- 1 < of_num n"
  using minus_of_num_less_of_num_iff [of One n] by (simp add: of_num_One)

lemma minus_one_less_one_iff: "- 1 < 1"
  using minus_of_num_less_of_num_iff [of One One] by (simp add: of_num_One)

lemma minus_of_num_le_of_num_iff: "- of_num m \<le> of_num n"
  by (simp add: less_imp_le minus_of_num_less_of_num_iff)

lemma minus_of_num_le_one_iff: "- of_num n \<le> 1"
  by (simp add: less_imp_le minus_of_num_less_one_iff)

lemma minus_one_le_of_num_iff: "- 1 \<le> of_num n"
  by (simp add: less_imp_le minus_one_less_of_num_iff)

lemma minus_one_le_one_iff: "- 1 \<le> 1"
  by (simp add: less_imp_le minus_one_less_one_iff)

lemma of_num_le_minus_of_num_iff: "\<not> of_num m \<le> - of_num n"
  by (simp add: not_le minus_of_num_less_of_num_iff)

lemma one_le_minus_of_num_iff: "\<not> 1 \<le> - of_num n"
  by (simp add: not_le minus_of_num_less_one_iff)

lemma of_num_le_minus_one_iff: "\<not> of_num n \<le> - 1"
  by (simp add: not_le minus_one_less_of_num_iff)

lemma one_le_minus_one_iff: "\<not> 1 \<le> - 1"
  by (simp add: not_le minus_one_less_one_iff)

lemma of_num_less_minus_of_num_iff: "\<not> of_num m < - of_num n"
  by (simp add: not_less minus_of_num_le_of_num_iff)

lemma one_less_minus_of_num_iff: "\<not> 1 < - of_num n"
  by (simp add: not_less minus_of_num_le_one_iff)

lemma of_num_less_minus_one_iff: "\<not> of_num n < - 1"
  by (simp add: not_less minus_one_le_of_num_iff)

lemma one_less_minus_one_iff: "\<not> 1 < - 1"
  by (simp add: not_less minus_one_le_one_iff)

lemmas le_signed_numeral_special [numeral] =
  minus_of_num_le_of_num_iff
  minus_of_num_le_one_iff
  minus_one_le_of_num_iff
  minus_one_le_one_iff
  of_num_le_minus_of_num_iff
  one_le_minus_of_num_iff
  of_num_le_minus_one_iff
  one_le_minus_one_iff

lemmas less_signed_numeral_special [numeral] =
  minus_of_num_less_of_num_iff
  minus_of_num_not_equal_of_num
  minus_of_num_less_one_iff
  minus_one_less_of_num_iff
  minus_one_less_one_iff
  of_num_less_minus_of_num_iff
  one_less_minus_of_num_iff
  of_num_less_minus_one_iff
  one_less_minus_one_iff

end

subsubsection {* Structures with subtraction: class @{text semiring_1_minus} *}

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
  of_num_plus of_num_eq_iff Dig_plus refl [of One, THEN eqTrueI] num.inject

simproc_setup numeral_minus ("of_num m - of_num n") = {*
  let
    (*TODO proper implicit use of morphism via pattern antiquotations*)
    fun cdest_of_num ct = (List.last o snd o Drule.strip_comb) ct;
    fun cdest_minus ct = case (rev o snd o Drule.strip_comb) ct of [n, m] => (m, n);
    fun attach_num ct = (dest_num (Thm.term_of ct), ct);
    fun cdifference t = (pairself (attach_num o cdest_of_num) o cdest_minus) t;
    val simplify = Raw_Simplifier.rewrite false (map mk_meta_eq @{thms Dig_plus_eval});
    fun cert ck cl cj = @{thm eqTrueE} OF [@{thm meta_eq_to_obj_eq}
      OF [simplify (Drule.list_comb (@{cterm "op = :: num \<Rightarrow> _"},
        [Drule.list_comb (@{cterm "op + :: num \<Rightarrow> _"}, [ck, cl]), cj]))]];
  in fn phi => fn _ => fn ct => case try cdifference ct
   of NONE => (NONE)
    | SOME ((k, ck), (l, cl)) => SOME (let val j = k - l in if j = 0
        then Raw_Simplifier.rewrite false [mk_meta_eq (Morphism.thm phi @{thm Dig_of_num_zero})] ct
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


subsubsection {* Structures with negation: class @{text ring_1} *}

context ring_1
begin

subclass semiring_1_minus proof
qed (simp_all add: algebra_simps)

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
  by simp_all

lemma of_int_of_num [numeral]: "of_int (of_num n) = of_num n"
by (induct n)
  (simp_all only: of_num.simps semiring_numeral_class.of_num.simps of_int_add, simp_all)

declare of_int_1 [numeral]

end


subsubsection {* Structures with exponentiation *}

lemma of_num_square: "of_num (square x) = of_num x * of_num x"
by (induct x)
   (simp_all add: of_num.simps of_num_add algebra_simps)

lemma of_num_pow: "of_num (pow x y) = of_num x ^ of_num y"
by (induct y)
   (simp_all add: of_num.simps of_num_square of_num_mult power_add)

lemma power_of_num [numeral]: "of_num x ^ of_num y = of_num (pow x y)"
  unfolding of_num_pow ..

lemma power_zero_of_num [numeral]:
  "0 ^ of_num n = (0::'a::semiring_1)"
  using of_num_pos [where n=n and ?'a=nat]
  by (simp add: power_0_left)

lemma power_minus_Dig0 [numeral]:
  fixes x :: "'a::ring_1"
  shows "(- x) ^ of_num (Dig0 n) = x ^ of_num (Dig0 n)"
  by (induct n rule: num_induct) (simp_all add: of_num.simps of_num_inc)

lemma power_minus_Dig1 [numeral]:
  fixes x :: "'a::ring_1"
  shows "(- x) ^ of_num (Dig1 n) = - (x ^ of_num (Dig1 n))"
  by (induct n rule: num_induct) (simp_all add: of_num.simps of_num_inc)

declare power_one [numeral]


subsubsection {* Greetings to @{typ nat}. *}

instance nat :: semiring_1_minus proof
qed simp_all

lemma Suc_of_num [numeral]: "Suc (of_num n) = of_num (n + One)"
  unfolding of_num_plus_one [symmetric] by simp

lemma nat_number:
  "1 = Suc 0"
  "of_num One = Suc 0"
  "of_num (Dig0 n) = Suc (of_num (DigM n))"
  "of_num (Dig1 n) = Suc (of_num (Dig0 n))"
  by (simp_all add: of_num.simps DigM_plus_one Suc_of_num)

declare diff_0_eq_0 [numeral]


subsection {* Proof tools setup *}

subsubsection {* Numeral equations as default simplification rules *}

declare (in semiring_numeral) of_num_One [simp]
declare (in semiring_numeral) of_num_plus_one [simp]
declare (in semiring_numeral) of_num_one_plus [simp]
declare (in semiring_numeral) of_num_plus [simp]
declare (in semiring_numeral) of_num_times [simp]

declare (in semiring_1) of_nat_of_num [simp]

declare (in semiring_char_0) of_num_eq_iff [simp]
declare (in semiring_char_0) of_num_eq_one_iff [simp]
declare (in semiring_char_0) one_eq_of_num_iff [simp]

declare (in linordered_semidom) of_num_pos [simp]
declare (in linordered_semidom) of_num_not_zero [simp]
declare (in linordered_semidom) of_num_less_eq_iff [simp]
declare (in linordered_semidom) of_num_less_eq_one_iff [simp]
declare (in linordered_semidom) one_less_eq_of_num_iff [simp]
declare (in linordered_semidom) of_num_less_iff [simp]
declare (in linordered_semidom) of_num_less_one_iff [simp]
declare (in linordered_semidom) one_less_of_num_iff [simp]
declare (in linordered_semidom) of_num_nonneg [simp]
declare (in linordered_semidom) of_num_less_zero_iff [simp]
declare (in linordered_semidom) of_num_le_zero_iff [simp]

declare (in linordered_idom) le_signed_numeral_special [simp]
declare (in linordered_idom) less_signed_numeral_special [simp]

declare (in semiring_1_minus) Dig_of_num_minus_one [simp]
declare (in semiring_1_minus) Dig_one_minus_of_num [simp]

declare (in ring_1) Dig_plus_uminus [simp]
declare (in ring_1) of_int_of_num [simp]

declare power_of_num [simp]
declare power_zero_of_num [simp]
declare power_minus_Dig0 [simp]
declare power_minus_Dig1 [simp]

declare Suc_of_num [simp]


subsubsection {* Reorientation of equalities *}

setup {*
  Reorient_Proc.add
    (fn Const(@{const_name of_num}, _) $ _ => true
      | Const(@{const_name uminus}, _) $
          (Const(@{const_name of_num}, _) $ _) => true
      | _ => false)
*}

simproc_setup reorient_num ("of_num n = x" | "- of_num m = y") = Reorient_Proc.proc


subsubsection {* Constant folding for multiplication in semirings *}

context semiring_numeral
begin

lemma mult_of_num_commute: "x * of_num n = of_num n * x"
by (induct n)
  (simp_all only: of_num.simps left_distrib right_distrib mult_1_left mult_1_right)

definition
  "commutes_with a b \<longleftrightarrow> a * b = b * a"

lemma commutes_with_commute: "commutes_with a b \<Longrightarrow> a * b = b * a"
unfolding commutes_with_def .

lemma commutes_with_left_commute: "commutes_with a b \<Longrightarrow> a * (b * c) = b * (a * c)"
unfolding commutes_with_def by (simp only: mult_assoc [symmetric])

lemma commutes_with_numeral: "commutes_with x (of_num n)" "commutes_with (of_num n) x"
unfolding commutes_with_def by (simp_all add: mult_of_num_commute)

lemmas mult_ac_numeral =
  mult_assoc
  commutes_with_commute
  commutes_with_left_commute
  commutes_with_numeral

end

ML {*
structure Semiring_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val assoc_ss = HOL_ss addsimps @{thms mult_ac_numeral}
  val eq_reflection = eq_reflection
  fun is_numeral (Const(@{const_name of_num}, _) $ _) = true
    | is_numeral _ = false;
end;

structure Semiring_Times_Assoc = Assoc_Fold (Semiring_Times_Assoc_Data);
*}

simproc_setup semiring_assoc_fold' ("(a::'a::semiring_numeral) * b") =
  {* fn phi => fn ss => fn ct =>
    Semiring_Times_Assoc.proc ss (Thm.term_of ct) *}


subsection {* Code generator setup for @{typ int} *}

text {* Reversing standard setup *}

lemma [code_unfold del]: "(0::int) \<equiv> Numeral0" by simp
lemma [code_unfold del]: "(1::int) \<equiv> Numeral1" by simp
declare zero_is_num_zero [code_unfold del]
declare one_is_num_one [code_unfold del]
  
lemma [code, code del]:
  "(1 :: int) = 1"
  "(op + :: int \<Rightarrow> int \<Rightarrow> int) = op +"
  "(uminus :: int \<Rightarrow> int) = uminus"
  "(op - :: int \<Rightarrow> int \<Rightarrow> int) = op -"
  "(op * :: int \<Rightarrow> int \<Rightarrow> int) = op *"
  "(HOL.equal :: int \<Rightarrow> int \<Rightarrow> bool) = HOL.equal"
  "(op \<le> :: int \<Rightarrow> int \<Rightarrow> bool) = op \<le>"
  "(op < :: int \<Rightarrow> int \<Rightarrow> bool) = op <"
  by rule+

text {* Constructors *}

definition Pls :: "num \<Rightarrow> int" where
  [simp, code_post]: "Pls n = of_num n"

definition Mns :: "num \<Rightarrow> int" where
  [simp, code_post]: "Mns n = - of_num n"

code_datatype "0::int" Pls Mns

lemmas [code_unfold] = Pls_def [symmetric] Mns_def [symmetric]

text {* Auxiliary operations *}

definition dup :: "int \<Rightarrow> int" where
  [simp]: "dup k = k + k"

lemma Dig_dup [code]:
  "dup 0 = 0"
  "dup (Pls n) = Pls (Dig0 n)"
  "dup (Mns n) = Mns (Dig0 n)"
  by (simp_all add: of_num.simps)

definition sub :: "num \<Rightarrow> num \<Rightarrow> int" where
  [simp]: "sub m n = (of_num m - of_num n)"

lemma Dig_sub [code]:
  "sub One One = 0"
  "sub (Dig0 m) One = of_num (DigM m)"
  "sub (Dig1 m) One = of_num (Dig0 m)"
  "sub One (Dig0 n) = - of_num (DigM n)"
  "sub One (Dig1 n) = - of_num (Dig0 n)"
  "sub (Dig0 m) (Dig0 n) = dup (sub m n)"
  "sub (Dig1 m) (Dig1 n) = dup (sub m n)"
  "sub (Dig1 m) (Dig0 n) = dup (sub m n) + 1"
  "sub (Dig0 m) (Dig1 n) = dup (sub m n) - 1"
  by (simp_all add: algebra_simps num_eq_iff nat_of_num_add)

text {* Implementations *}

lemma one_int_code [code]:
  "1 = Pls One"
  by simp

lemma plus_int_code [code]:
  "k + 0 = (k::int)"
  "0 + l = (l::int)"
  "Pls m + Pls n = Pls (m + n)"
  "Pls m + Mns n = sub m n"
  "Mns m + Pls n = sub n m"
  "Mns m + Mns n = Mns (m + n)"
  by simp_all

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
  by simp_all

lemma times_int_code [code]:
  "k * 0 = (0::int)"
  "0 * l = (0::int)"
  "Pls m * Pls n = Pls (m * n)"
  "Pls m * Mns n = Mns (m * n)"
  "Mns m * Pls n = Mns (m * n)"
  "Mns m * Mns n = Pls (m * n)"
  by simp_all

lemma eq_int_code [code]:
  "HOL.equal 0 (0::int) \<longleftrightarrow> True"
  "HOL.equal 0 (Pls l) \<longleftrightarrow> False"
  "HOL.equal 0 (Mns l) \<longleftrightarrow> False"
  "HOL.equal (Pls k) 0 \<longleftrightarrow> False"
  "HOL.equal (Pls k) (Pls l) \<longleftrightarrow> HOL.equal k l"
  "HOL.equal (Pls k) (Mns l) \<longleftrightarrow> False"
  "HOL.equal (Mns k) 0 \<longleftrightarrow> False"
  "HOL.equal (Mns k) (Pls l) \<longleftrightarrow> False"
  "HOL.equal (Mns k) (Mns l) \<longleftrightarrow> HOL.equal k l"
  by (auto simp add: equal dest: sym)

lemma [code nbe]:
  "HOL.equal (k::int) k \<longleftrightarrow> True"
  by (fact equal_refl)

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
  by simp_all

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
  by simp_all

hide_const (open) sub dup

text {* Pretty literals *}

ML {*
local open Code_Thingol in

fun add_code print target =
  let
    fun dest_num one' dig0' dig1' thm =
      let
        fun dest_dig (IConst (c, _)) = if c = dig0' then 0
              else if c = dig1' then 1
              else Code_Printer.eqn_error thm "Illegal numeral expression: illegal dig"
          | dest_dig _ = Code_Printer.eqn_error thm "Illegal numeral expression: illegal digit";
        fun dest_num (IConst (c, _)) = if c = one' then 1
              else Code_Printer.eqn_error thm "Illegal numeral expression: illegal leading digit"
          | dest_num (t1 `$ t2) = 2 * dest_num t2 + dest_dig t1
          | dest_num _ = Code_Printer.eqn_error thm "Illegal numeral expression: illegal term";
      in dest_num end;
    fun pretty sgn literals [one', dig0', dig1'] _ thm _ _ [(t, _)] =
      (Code_Printer.str o print literals o sgn o dest_num one' dig0' dig1' thm) t
    fun add_syntax (c, sgn) = Code_Target.add_const_syntax target c
      (SOME (Code_Printer.complex_const_syntax
        (1, ([@{const_name One}, @{const_name Dig0}, @{const_name Dig1}],
          pretty sgn))));
  in
    add_syntax (@{const_name Pls}, I)
    #> add_syntax (@{const_name Mns}, (fn k => ~ k))
  end;

end
*}

hide_const (open) One Dig0 Dig1


subsection {* Toy examples *}

definition "foo \<longleftrightarrow> #4 * #2 + #7 = (#8 :: nat)"
definition "bar \<longleftrightarrow> #4 * #2 + #7 \<ge> (#8 :: int) - #3"

code_thms foo bar
export_code foo bar checking SML OCaml? Haskell? Scala?

text {* This is an ad-hoc @{text Code_Integer} setup. *}

setup {*
  fold (add_code Code_Printer.literal_numeral)
    [Code_ML.target_SML, Code_ML.target_OCaml, Code_Haskell.target, Code_Scala.target]
*}

code_type int
  (SML "IntInf.int")
  (OCaml "Big'_int.big'_int")
  (Haskell "Integer")
  (Scala "BigInt")
  (Eval "int")

code_const "0::int"
  (SML "0/ :/ IntInf.int")
  (OCaml "Big'_int.zero")
  (Haskell "0")
  (Scala "BigInt(0)")
  (Eval "0/ :/ int")

code_const Int.pred
  (SML "IntInf.- ((_), 1)")
  (OCaml "Big'_int.pred'_big'_int")
  (Haskell "!(_/ -/ 1)")
  (Scala "!(_ -/ 1)")
  (Eval "!(_/ -/ 1)")

code_const Int.succ
  (SML "IntInf.+ ((_), 1)")
  (OCaml "Big'_int.succ'_big'_int")
  (Haskell "!(_/ +/ 1)")
  (Scala "!(_ +/ 1)")
  (Eval "!(_/ +/ 1)")

code_const "op + \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "IntInf.+ ((_), (_))")
  (OCaml "Big'_int.add'_big'_int")
  (Haskell infixl 6 "+")
  (Scala infixl 7 "+")
  (Eval infixl 8 "+")

code_const "uminus \<Colon> int \<Rightarrow> int"
  (SML "IntInf.~")
  (OCaml "Big'_int.minus'_big'_int")
  (Haskell "negate")
  (Scala "!(- _)")
  (Eval "~/ _")

code_const "op - \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "IntInf.- ((_), (_))")
  (OCaml "Big'_int.sub'_big'_int")
  (Haskell infixl 6 "-")
  (Scala infixl 7 "-")
  (Eval infixl 8 "-")

code_const "op * \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "IntInf.* ((_), (_))")
  (OCaml "Big'_int.mult'_big'_int")
  (Haskell infixl 7 "*")
  (Scala infixl 8 "*")
  (Eval infixl 9 "*")

code_const pdivmod
  (SML "IntInf.divMod/ (IntInf.abs _,/ IntInf.abs _)")
  (OCaml "Big'_int.quomod'_big'_int/ (Big'_int.abs'_big'_int _)/ (Big'_int.abs'_big'_int _)")
  (Haskell "divMod/ (abs _)/ (abs _)")
  (Scala "!((k: BigInt) => (l: BigInt) =>/ if (l == 0)/ (BigInt(0), k) else/ (k.abs '/% l.abs))")
  (Eval "Integer.div'_mod/ (abs _)/ (abs _)")

code_const "HOL.equal \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "!((_ : IntInf.int) = _)")
  (OCaml "Big'_int.eq'_big'_int")
  (Haskell infix 4 "==")
  (Scala infixl 5 "==")
  (Eval infixl 6 "=")

code_const "op \<le> \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "IntInf.<= ((_), (_))")
  (OCaml "Big'_int.le'_big'_int")
  (Haskell infix 4 "<=")
  (Scala infixl 4 "<=")
  (Eval infixl 6 "<=")

code_const "op < \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "IntInf.< ((_), (_))")
  (OCaml "Big'_int.lt'_big'_int")
  (Haskell infix 4 "<")
  (Scala infixl 4 "<")
  (Eval infixl 6 "<")

code_const Code_Numeral.int_of
  (SML "IntInf.fromInt")
  (OCaml "_")
  (Haskell "toInteger")
  (Scala "!_.as'_BigInt")
  (Eval "_")

export_code foo bar checking SML OCaml? Haskell? Scala?

end
