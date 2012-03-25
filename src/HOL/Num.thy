(*  Title:      HOL/Num.thy
    Author:     Florian Haftmann
    Author:     Brian Huffman
*)

header {* Binary Numerals *}

theory Num
imports Datatype Power
begin

subsection {* The @{text num} type *}

datatype num = One | Bit0 num | Bit1 num

text {* Increment function for type @{typ num} *}

primrec inc :: "num \<Rightarrow> num" where
  "inc One = Bit0 One" |
  "inc (Bit0 x) = Bit1 x" |
  "inc (Bit1 x) = Bit0 (inc x)"

text {* Converting between type @{typ num} and type @{typ nat} *}

primrec nat_of_num :: "num \<Rightarrow> nat" where
  "nat_of_num One = Suc 0" |
  "nat_of_num (Bit0 x) = nat_of_num x + nat_of_num x" |
  "nat_of_num (Bit1 x) = Suc (nat_of_num x + nat_of_num x)"

primrec num_of_nat :: "nat \<Rightarrow> num" where
  "num_of_nat 0 = One" |
  "num_of_nat (Suc n) = (if 0 < n then inc (num_of_nat n) else One)"

lemma nat_of_num_pos: "0 < nat_of_num x"
  by (induct x) simp_all

lemma nat_of_num_neq_0: " nat_of_num x \<noteq> 0"
  by (induct x) simp_all

lemma nat_of_num_inc: "nat_of_num (inc x) = Suc (nat_of_num x)"
  by (induct x) simp_all

lemma num_of_nat_double:
  "0 < n \<Longrightarrow> num_of_nat (n + n) = Bit0 (num_of_nat n)"
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
  apply safe
  apply (drule arg_cong [where f=num_of_nat])
  apply (simp add: nat_of_num_inverse)
  done

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
  From now on, there are two possible models for @{typ num}:
  as positive naturals (rule @{text "num_induct"})
  and as digit representation (rules @{text "num.induct"}, @{text "num.cases"}).
*}


subsection {* Numeral operations *}

instantiation num :: "{plus,times,linorder}"
begin

definition [code del]:
  "m + n = num_of_nat (nat_of_num m + nat_of_num n)"

definition [code del]:
  "m * n = num_of_nat (nat_of_num m * nat_of_num n)"

definition [code del]:
  "m \<le> n \<longleftrightarrow> nat_of_num m \<le> nat_of_num n"

definition [code del]:
  "m < n \<longleftrightarrow> nat_of_num m < nat_of_num n"

instance
  by (default, auto simp add: less_num_def less_eq_num_def num_eq_iff)

end

lemma nat_of_num_add: "nat_of_num (x + y) = nat_of_num x + nat_of_num y"
  unfolding plus_num_def
  by (intro num_of_nat_inverse add_pos_pos nat_of_num_pos)

lemma nat_of_num_mult: "nat_of_num (x * y) = nat_of_num x * nat_of_num y"
  unfolding times_num_def
  by (intro num_of_nat_inverse mult_pos_pos nat_of_num_pos)

lemma add_num_simps [simp, code]:
  "One + One = Bit0 One"
  "One + Bit0 n = Bit1 n"
  "One + Bit1 n = Bit0 (n + One)"
  "Bit0 m + One = Bit1 m"
  "Bit0 m + Bit0 n = Bit0 (m + n)"
  "Bit0 m + Bit1 n = Bit1 (m + n)"
  "Bit1 m + One = Bit0 (m + One)"
  "Bit1 m + Bit0 n = Bit1 (m + n)"
  "Bit1 m + Bit1 n = Bit0 (m + n + One)"
  by (simp_all add: num_eq_iff nat_of_num_add)

lemma mult_num_simps [simp, code]:
  "m * One = m"
  "One * n = n"
  "Bit0 m * Bit0 n = Bit0 (Bit0 (m * n))"
  "Bit0 m * Bit1 n = Bit0 (m * Bit1 n)"
  "Bit1 m * Bit0 n = Bit0 (Bit1 m * n)"
  "Bit1 m * Bit1 n = Bit1 (m + n + Bit0 (m * n))"
  by (simp_all add: num_eq_iff nat_of_num_add
    nat_of_num_mult left_distrib right_distrib)

lemma eq_num_simps:
  "One = One \<longleftrightarrow> True"
  "One = Bit0 n \<longleftrightarrow> False"
  "One = Bit1 n \<longleftrightarrow> False"
  "Bit0 m = One \<longleftrightarrow> False"
  "Bit1 m = One \<longleftrightarrow> False"
  "Bit0 m = Bit0 n \<longleftrightarrow> m = n"
  "Bit0 m = Bit1 n \<longleftrightarrow> False"
  "Bit1 m = Bit0 n \<longleftrightarrow> False"
  "Bit1 m = Bit1 n \<longleftrightarrow> m = n"
  by simp_all

lemma le_num_simps [simp, code]:
  "One \<le> n \<longleftrightarrow> True"
  "Bit0 m \<le> One \<longleftrightarrow> False"
  "Bit1 m \<le> One \<longleftrightarrow> False"
  "Bit0 m \<le> Bit0 n \<longleftrightarrow> m \<le> n"
  "Bit0 m \<le> Bit1 n \<longleftrightarrow> m \<le> n"
  "Bit1 m \<le> Bit1 n \<longleftrightarrow> m \<le> n"
  "Bit1 m \<le> Bit0 n \<longleftrightarrow> m < n"
  using nat_of_num_pos [of n] nat_of_num_pos [of m]
  by (auto simp add: less_eq_num_def less_num_def)

lemma less_num_simps [simp, code]:
  "m < One \<longleftrightarrow> False"
  "One < Bit0 n \<longleftrightarrow> True"
  "One < Bit1 n \<longleftrightarrow> True"
  "Bit0 m < Bit0 n \<longleftrightarrow> m < n"
  "Bit0 m < Bit1 n \<longleftrightarrow> m \<le> n"
  "Bit1 m < Bit1 n \<longleftrightarrow> m < n"
  "Bit1 m < Bit0 n \<longleftrightarrow> m < n"
  using nat_of_num_pos [of n] nat_of_num_pos [of m]
  by (auto simp add: less_eq_num_def less_num_def)

text {* Rules using @{text One} and @{text inc} as constructors *}

lemma add_One: "x + One = inc x"
  by (simp add: num_eq_iff nat_of_num_add nat_of_num_inc)

lemma add_One_commute: "One + n = n + One"
  by (induct n) simp_all

lemma add_inc: "x + inc y = inc (x + y)"
  by (simp add: num_eq_iff nat_of_num_add nat_of_num_inc)

lemma mult_inc: "x * inc y = x * y + x"
  by (simp add: num_eq_iff nat_of_num_mult nat_of_num_add nat_of_num_inc)

text {* The @{const num_of_nat} conversion *}

lemma num_of_nat_One:
  "n \<le> 1 \<Longrightarrow> num_of_nat n = Num.One"
  by (cases n) simp_all

lemma num_of_nat_plus_distrib:
  "0 < m \<Longrightarrow> 0 < n \<Longrightarrow> num_of_nat (m + n) = num_of_nat m + num_of_nat n"
  by (induct n) (auto simp add: add_One add_One_commute add_inc)

text {* A double-and-decrement function *}

primrec BitM :: "num \<Rightarrow> num" where
  "BitM One = One" |
  "BitM (Bit0 n) = Bit1 (BitM n)" |
  "BitM (Bit1 n) = Bit1 (Bit0 n)"

lemma BitM_plus_one: "BitM n + One = Bit0 n"
  by (induct n) simp_all

lemma one_plus_BitM: "One + BitM n = Bit0 n"
  unfolding add_One_commute BitM_plus_one ..

text {* Squaring and exponentiation *}

primrec sqr :: "num \<Rightarrow> num" where
  "sqr One = One" |
  "sqr (Bit0 n) = Bit0 (Bit0 (sqr n))" |
  "sqr (Bit1 n) = Bit1 (Bit0 (sqr n + n))"

primrec pow :: "num \<Rightarrow> num \<Rightarrow> num" where
  "pow x One = x" |
  "pow x (Bit0 y) = sqr (pow x y)" |
  "pow x (Bit1 y) = x * sqr (pow x y)"

lemma nat_of_num_sqr: "nat_of_num (sqr x) = nat_of_num x * nat_of_num x"
  by (induct x, simp_all add: algebra_simps nat_of_num_add)

lemma sqr_conv_mult: "sqr x = x * x"
  by (simp add: num_eq_iff nat_of_num_sqr nat_of_num_mult)


subsection {* Numary numerals *}

text {*
  We embed numary representations into a generic algebraic
  structure using @{text numeral}.
*}

class numeral = one + semigroup_add
begin

primrec numeral :: "num \<Rightarrow> 'a" where
  numeral_One: "numeral One = 1" |
  numeral_Bit0: "numeral (Bit0 n) = numeral n + numeral n" |
  numeral_Bit1: "numeral (Bit1 n) = numeral n + numeral n + 1"

lemma one_plus_numeral_commute: "1 + numeral x = numeral x + 1"
  apply (induct x)
  apply simp
  apply (simp add: add_assoc [symmetric], simp add: add_assoc)
  apply (simp add: add_assoc [symmetric], simp add: add_assoc)
  done

lemma numeral_inc: "numeral (inc x) = numeral x + 1"
proof (induct x)
  case (Bit1 x)
  have "numeral x + (1 + numeral x) + 1 = numeral x + (numeral x + 1) + 1"
    by (simp only: one_plus_numeral_commute)
  with Bit1 show ?case
    by (simp add: add_assoc)
qed simp_all

declare numeral.simps [simp del]

abbreviation "Numeral1 \<equiv> numeral One"

declare numeral_One [code_post]

end

text {* Negative numerals. *}

class neg_numeral = numeral + group_add
begin

definition neg_numeral :: "num \<Rightarrow> 'a" where
  "neg_numeral k = - numeral k"

end

text {* Numeral syntax. *}

syntax
  "_Numeral" :: "num_const \<Rightarrow> 'a"    ("_")

parse_translation {*
let
  fun num_of_int n = if n > 0 then case IntInf.quotRem (n, 2)
     of (0, 1) => Syntax.const @{const_name One}
      | (n, 0) => Syntax.const @{const_name Bit0} $ num_of_int n
      | (n, 1) => Syntax.const @{const_name Bit1} $ num_of_int n
    else raise Match;
  val pos = Syntax.const @{const_name numeral}
  val neg = Syntax.const @{const_name neg_numeral}
  val one = Syntax.const @{const_name Groups.one}
  val zero = Syntax.const @{const_name Groups.zero}
  fun numeral_tr [(c as Const (@{syntax_const "_constrain"}, _)) $ t $ u] =
        c $ numeral_tr [t] $ u
    | numeral_tr [Const (num, _)] =
        let
          val {value, ...} = Lexicon.read_xnum num;
        in
          if value = 0 then zero else
          if value > 0
          then pos $ num_of_int value
          else neg $ num_of_int (~value)
        end
    | numeral_tr ts = raise TERM ("numeral_tr", ts);
in [("_Numeral", numeral_tr)] end
*}

typed_print_translation (advanced) {*
let
  fun dest_num (Const (@{const_syntax Bit0}, _) $ n) = 2 * dest_num n
    | dest_num (Const (@{const_syntax Bit1}, _) $ n) = 2 * dest_num n + 1
    | dest_num (Const (@{const_syntax One}, _)) = 1;
  fun num_tr' sign ctxt T [n] =
    let
      val k = dest_num n;
      val t' = Syntax.const @{syntax_const "_Numeral"} $
        Syntax.free (sign ^ string_of_int k);
    in
      case T of
        Type (@{type_name fun}, [_, T']) =>
          if not (Config.get ctxt show_types) andalso can Term.dest_Type T' then t'
          else Syntax.const @{syntax_const "_constrain"} $ t' $ Syntax_Phases.term_of_typ ctxt T'
      | T' => if T' = dummyT then t' else raise Match
    end;
in [(@{const_syntax numeral}, num_tr' ""),
    (@{const_syntax neg_numeral}, num_tr' "-")] end
*}

subsection {* Class-specific numeral rules *}

text {*
  @{const numeral} is a morphism.
*}

subsubsection {* Structures with addition: class @{text numeral} *}

context numeral
begin

lemma numeral_add: "numeral (m + n) = numeral m + numeral n"
  by (induct n rule: num_induct)
     (simp_all only: numeral_One add_One add_inc numeral_inc add_assoc)

lemma numeral_plus_numeral: "numeral m + numeral n = numeral (m + n)"
  by (rule numeral_add [symmetric])

lemma numeral_plus_one: "numeral n + 1 = numeral (n + One)"
  using numeral_add [of n One] by (simp add: numeral_One)

lemma one_plus_numeral: "1 + numeral n = numeral (One + n)"
  using numeral_add [of One n] by (simp add: numeral_One)

lemma one_add_one: "1 + 1 = 2"
  using numeral_add [of One One] by (simp add: numeral_One)

lemmas add_numeral_special =
  numeral_plus_one one_plus_numeral one_add_one

end

subsubsection {*
  Structures with negation: class @{text neg_numeral}
*}

context neg_numeral
begin

text {* Numerals form an abelian subgroup. *}

inductive is_num :: "'a \<Rightarrow> bool" where
  "is_num 1" |
  "is_num x \<Longrightarrow> is_num (- x)" |
  "\<lbrakk>is_num x; is_num y\<rbrakk> \<Longrightarrow> is_num (x + y)"

lemma is_num_numeral: "is_num (numeral k)"
  by (induct k, simp_all add: numeral.simps is_num.intros)

lemma is_num_add_commute:
  "\<lbrakk>is_num x; is_num y\<rbrakk> \<Longrightarrow> x + y = y + x"
  apply (induct x rule: is_num.induct)
  apply (induct y rule: is_num.induct)
  apply simp
  apply (rule_tac a=x in add_left_imp_eq)
  apply (rule_tac a=x in add_right_imp_eq)
  apply (simp add: add_assoc minus_add_cancel)
  apply (simp add: add_assoc [symmetric], simp add: add_assoc)
  apply (rule_tac a=x in add_left_imp_eq)
  apply (rule_tac a=x in add_right_imp_eq)
  apply (simp add: add_assoc minus_add_cancel add_minus_cancel)
  apply (simp add: add_assoc, simp add: add_assoc [symmetric])
  done

lemma is_num_add_left_commute:
  "\<lbrakk>is_num x; is_num y\<rbrakk> \<Longrightarrow> x + (y + z) = y + (x + z)"
  by (simp only: add_assoc [symmetric] is_num_add_commute)

lemmas is_num_normalize =
  add_assoc is_num_add_commute is_num_add_left_commute
  is_num.intros is_num_numeral
  diff_minus minus_add add_minus_cancel minus_add_cancel

definition dbl :: "'a \<Rightarrow> 'a" where "dbl x = x + x"
definition dbl_inc :: "'a \<Rightarrow> 'a" where "dbl_inc x = x + x + 1"
definition dbl_dec :: "'a \<Rightarrow> 'a" where "dbl_dec x = x + x - 1"

definition sub :: "num \<Rightarrow> num \<Rightarrow> 'a" where
  "sub k l = numeral k - numeral l"

lemma numeral_BitM: "numeral (BitM n) = numeral (Bit0 n) - 1"
  by (simp only: BitM_plus_one [symmetric] numeral_add numeral_One eq_diff_eq)

lemma dbl_simps [simp]:
  "dbl (neg_numeral k) = neg_numeral (Bit0 k)"
  "dbl 0 = 0"
  "dbl 1 = 2"
  "dbl (numeral k) = numeral (Bit0 k)"
  unfolding dbl_def neg_numeral_def numeral.simps
  by (simp_all add: minus_add)

lemma dbl_inc_simps [simp]:
  "dbl_inc (neg_numeral k) = neg_numeral (BitM k)"
  "dbl_inc 0 = 1"
  "dbl_inc 1 = 3"
  "dbl_inc (numeral k) = numeral (Bit1 k)"
  unfolding dbl_inc_def neg_numeral_def numeral.simps numeral_BitM
  by (simp_all add: is_num_normalize)

lemma dbl_dec_simps [simp]:
  "dbl_dec (neg_numeral k) = neg_numeral (Bit1 k)"
  "dbl_dec 0 = -1"
  "dbl_dec 1 = 1"
  "dbl_dec (numeral k) = numeral (BitM k)"
  unfolding dbl_dec_def neg_numeral_def numeral.simps numeral_BitM
  by (simp_all add: is_num_normalize)

lemma sub_num_simps [simp]:
  "sub One One = 0"
  "sub One (Bit0 l) = neg_numeral (BitM l)"
  "sub One (Bit1 l) = neg_numeral (Bit0 l)"
  "sub (Bit0 k) One = numeral (BitM k)"
  "sub (Bit1 k) One = numeral (Bit0 k)"
  "sub (Bit0 k) (Bit0 l) = dbl (sub k l)"
  "sub (Bit0 k) (Bit1 l) = dbl_dec (sub k l)"
  "sub (Bit1 k) (Bit0 l) = dbl_inc (sub k l)"
  "sub (Bit1 k) (Bit1 l) = dbl (sub k l)"
  unfolding dbl_def dbl_dec_def dbl_inc_def sub_def
  unfolding neg_numeral_def numeral.simps numeral_BitM
  by (simp_all add: is_num_normalize)

lemma add_neg_numeral_simps:
  "numeral m + neg_numeral n = sub m n"
  "neg_numeral m + numeral n = sub n m"
  "neg_numeral m + neg_numeral n = neg_numeral (m + n)"
  unfolding sub_def diff_minus neg_numeral_def numeral_add numeral.simps
  by (simp_all add: is_num_normalize)

lemma add_neg_numeral_special:
  "1 + neg_numeral m = sub One m"
  "neg_numeral m + 1 = sub One m"
  unfolding sub_def diff_minus neg_numeral_def numeral_add numeral.simps
  by (simp_all add: is_num_normalize)

lemma diff_numeral_simps:
  "numeral m - numeral n = sub m n"
  "numeral m - neg_numeral n = numeral (m + n)"
  "neg_numeral m - numeral n = neg_numeral (m + n)"
  "neg_numeral m - neg_numeral n = sub n m"
  unfolding neg_numeral_def sub_def diff_minus numeral_add numeral.simps
  by (simp_all add: is_num_normalize)

lemma diff_numeral_special:
  "1 - numeral n = sub One n"
  "1 - neg_numeral n = numeral (One + n)"
  "numeral m - 1 = sub m One"
  "neg_numeral m - 1 = neg_numeral (m + One)"
  unfolding neg_numeral_def sub_def diff_minus numeral_add numeral.simps
  by (simp_all add: is_num_normalize)

lemma minus_one: "- 1 = -1"
  unfolding neg_numeral_def numeral.simps ..

lemma minus_numeral: "- numeral n = neg_numeral n"
  unfolding neg_numeral_def ..

lemma minus_neg_numeral: "- neg_numeral n = numeral n"
  unfolding neg_numeral_def by simp

lemmas minus_numeral_simps [simp] =
  minus_one minus_numeral minus_neg_numeral

end

subsubsection {*
  Structures with multiplication: class @{text semiring_numeral}
*}

class semiring_numeral = semiring + monoid_mult
begin

subclass numeral ..

lemma numeral_mult: "numeral (m * n) = numeral m * numeral n"
  apply (induct n rule: num_induct)
  apply (simp add: numeral_One)
  apply (simp add: mult_inc numeral_inc numeral_add numeral_inc right_distrib)
  done

lemma numeral_times_numeral: "numeral m * numeral n = numeral (m * n)"
  by (rule numeral_mult [symmetric])

end

subsubsection {*
  Structures with a zero: class @{text semiring_1}
*}

context semiring_1
begin

subclass semiring_numeral ..

lemma of_nat_numeral [simp]: "of_nat (numeral n) = numeral n"
  by (induct n,
    simp_all only: numeral.simps numeral_class.numeral.simps of_nat_add of_nat_1)

end

lemma nat_of_num_numeral: "nat_of_num = numeral"
proof
  fix n
  have "numeral n = nat_of_num n"
    by (induct n) (simp_all add: numeral.simps)
  then show "nat_of_num n = numeral n" by simp
qed

subsubsection {*
  Equality: class @{text semiring_char_0}
*}

context semiring_char_0
begin

lemma numeral_eq_iff: "numeral m = numeral n \<longleftrightarrow> m = n"
  unfolding of_nat_numeral [symmetric] nat_of_num_numeral [symmetric]
    of_nat_eq_iff num_eq_iff ..

lemma numeral_eq_one_iff: "numeral n = 1 \<longleftrightarrow> n = One"
  by (rule numeral_eq_iff [of n One, unfolded numeral_One])

lemma one_eq_numeral_iff: "1 = numeral n \<longleftrightarrow> One = n"
  by (rule numeral_eq_iff [of One n, unfolded numeral_One])

lemma numeral_neq_zero: "numeral n \<noteq> 0"
  unfolding of_nat_numeral [symmetric] nat_of_num_numeral [symmetric]
  by (simp add: nat_of_num_pos)

lemma zero_neq_numeral: "0 \<noteq> numeral n"
  unfolding eq_commute [of 0] by (rule numeral_neq_zero)

lemmas eq_numeral_simps [simp] =
  numeral_eq_iff
  numeral_eq_one_iff
  one_eq_numeral_iff
  numeral_neq_zero
  zero_neq_numeral

end

subsubsection {*
  Comparisons: class @{text linordered_semidom}
*}

text {*  Could be perhaps more general than here. *}

context linordered_semidom
begin

lemma numeral_le_iff: "numeral m \<le> numeral n \<longleftrightarrow> m \<le> n"
proof -
  have "of_nat (numeral m) \<le> of_nat (numeral n) \<longleftrightarrow> m \<le> n"
    unfolding less_eq_num_def nat_of_num_numeral of_nat_le_iff ..
  then show ?thesis by simp
qed

lemma one_le_numeral: "1 \<le> numeral n"
using numeral_le_iff [of One n] by (simp add: numeral_One)

lemma numeral_le_one_iff: "numeral n \<le> 1 \<longleftrightarrow> n \<le> One"
using numeral_le_iff [of n One] by (simp add: numeral_One)

lemma numeral_less_iff: "numeral m < numeral n \<longleftrightarrow> m < n"
proof -
  have "of_nat (numeral m) < of_nat (numeral n) \<longleftrightarrow> m < n"
    unfolding less_num_def nat_of_num_numeral of_nat_less_iff ..
  then show ?thesis by simp
qed

lemma not_numeral_less_one: "\<not> numeral n < 1"
  using numeral_less_iff [of n One] by (simp add: numeral_One)

lemma one_less_numeral_iff: "1 < numeral n \<longleftrightarrow> One < n"
  using numeral_less_iff [of One n] by (simp add: numeral_One)

lemma zero_le_numeral: "0 \<le> numeral n"
  by (induct n) (simp_all add: numeral.simps)

lemma zero_less_numeral: "0 < numeral n"
  by (induct n) (simp_all add: numeral.simps add_pos_pos)

lemma not_numeral_le_zero: "\<not> numeral n \<le> 0"
  by (simp add: not_le zero_less_numeral)

lemma not_numeral_less_zero: "\<not> numeral n < 0"
  by (simp add: not_less zero_le_numeral)

lemmas le_numeral_extra =
  zero_le_one not_one_le_zero
  order_refl [of 0] order_refl [of 1]

lemmas less_numeral_extra =
  zero_less_one not_one_less_zero
  less_irrefl [of 0] less_irrefl [of 1]

lemmas le_numeral_simps [simp] =
  numeral_le_iff
  one_le_numeral
  numeral_le_one_iff
  zero_le_numeral
  not_numeral_le_zero

lemmas less_numeral_simps [simp] =
  numeral_less_iff
  one_less_numeral_iff
  not_numeral_less_one
  zero_less_numeral
  not_numeral_less_zero

end

subsubsection {*
  Multiplication and negation: class @{text ring_1}
*}

context ring_1
begin

subclass neg_numeral ..

lemma mult_neg_numeral_simps:
  "neg_numeral m * neg_numeral n = numeral (m * n)"
  "neg_numeral m * numeral n = neg_numeral (m * n)"
  "numeral m * neg_numeral n = neg_numeral (m * n)"
  unfolding neg_numeral_def mult_minus_left mult_minus_right
  by (simp_all only: minus_minus numeral_mult)

lemma mult_minus1 [simp]: "-1 * z = - z"
  unfolding neg_numeral_def numeral.simps mult_minus_left by simp

lemma mult_minus1_right [simp]: "z * -1 = - z"
  unfolding neg_numeral_def numeral.simps mult_minus_right by simp

end

subsubsection {*
  Equality using @{text iszero} for rings with non-zero characteristic
*}

context ring_1
begin

definition iszero :: "'a \<Rightarrow> bool"
  where "iszero z \<longleftrightarrow> z = 0"

lemma iszero_0 [simp]: "iszero 0"
  by (simp add: iszero_def)

lemma not_iszero_1 [simp]: "\<not> iszero 1"
  by (simp add: iszero_def)

lemma not_iszero_Numeral1: "\<not> iszero Numeral1"
  by (simp add: numeral_One)

lemma iszero_neg_numeral [simp]:
  "iszero (neg_numeral w) \<longleftrightarrow> iszero (numeral w)"
  unfolding iszero_def neg_numeral_def
  by (rule neg_equal_0_iff_equal)

lemma eq_iff_iszero_diff: "x = y \<longleftrightarrow> iszero (x - y)"
  unfolding iszero_def by (rule eq_iff_diff_eq_0)

text {* The @{text "eq_numeral_iff_iszero"} lemmas are not declared
@{text "[simp]"} by default, because for rings of characteristic zero,
better simp rules are possible. For a type like integers mod @{text
"n"}, type-instantiated versions of these rules should be added to the
simplifier, along with a type-specific rule for deciding propositions
of the form @{text "iszero (numeral w)"}.

bh: Maybe it would not be so bad to just declare these as simp
rules anyway? I should test whether these rules take precedence over
the @{text "ring_char_0"} rules in the simplifier.
*}

lemma eq_numeral_iff_iszero:
  "numeral x = numeral y \<longleftrightarrow> iszero (sub x y)"
  "numeral x = neg_numeral y \<longleftrightarrow> iszero (numeral (x + y))"
  "neg_numeral x = numeral y \<longleftrightarrow> iszero (numeral (x + y))"
  "neg_numeral x = neg_numeral y \<longleftrightarrow> iszero (sub y x)"
  "numeral x = 1 \<longleftrightarrow> iszero (sub x One)"
  "1 = numeral y \<longleftrightarrow> iszero (sub One y)"
  "neg_numeral x = 1 \<longleftrightarrow> iszero (numeral (x + One))"
  "1 = neg_numeral y \<longleftrightarrow> iszero (numeral (One + y))"
  "numeral x = 0 \<longleftrightarrow> iszero (numeral x)"
  "0 = numeral y \<longleftrightarrow> iszero (numeral y)"
  "neg_numeral x = 0 \<longleftrightarrow> iszero (numeral x)"
  "0 = neg_numeral y \<longleftrightarrow> iszero (numeral y)"
  unfolding eq_iff_iszero_diff diff_numeral_simps diff_numeral_special
  by simp_all

end

subsubsection {*
  Equality and negation: class @{text ring_char_0}
*}

class ring_char_0 = ring_1 + semiring_char_0
begin

lemma not_iszero_numeral [simp]: "\<not> iszero (numeral w)"
  by (simp add: iszero_def)

lemma neg_numeral_eq_iff: "neg_numeral m = neg_numeral n \<longleftrightarrow> m = n"
  by (simp only: neg_numeral_def neg_equal_iff_equal numeral_eq_iff)

lemma numeral_neq_neg_numeral: "numeral m \<noteq> neg_numeral n"
  unfolding neg_numeral_def eq_neg_iff_add_eq_0
  by (simp add: numeral_plus_numeral)

lemma neg_numeral_neq_numeral: "neg_numeral m \<noteq> numeral n"
  by (rule numeral_neq_neg_numeral [symmetric])

lemma zero_neq_neg_numeral: "0 \<noteq> neg_numeral n"
  unfolding neg_numeral_def neg_0_equal_iff_equal by simp

lemma neg_numeral_neq_zero: "neg_numeral n \<noteq> 0"
  unfolding neg_numeral_def neg_equal_0_iff_equal by simp

lemma one_neq_neg_numeral: "1 \<noteq> neg_numeral n"
  using numeral_neq_neg_numeral [of One n] by (simp add: numeral_One)

lemma neg_numeral_neq_one: "neg_numeral n \<noteq> 1"
  using neg_numeral_neq_numeral [of n One] by (simp add: numeral_One)

lemmas eq_neg_numeral_simps [simp] =
  neg_numeral_eq_iff
  numeral_neq_neg_numeral neg_numeral_neq_numeral
  one_neq_neg_numeral neg_numeral_neq_one
  zero_neq_neg_numeral neg_numeral_neq_zero

end

subsubsection {*
  Structures with negation and order: class @{text linordered_idom}
*}

context linordered_idom
begin

subclass ring_char_0 ..

lemma neg_numeral_le_iff: "neg_numeral m \<le> neg_numeral n \<longleftrightarrow> n \<le> m"
  by (simp only: neg_numeral_def neg_le_iff_le numeral_le_iff)

lemma neg_numeral_less_iff: "neg_numeral m < neg_numeral n \<longleftrightarrow> n < m"
  by (simp only: neg_numeral_def neg_less_iff_less numeral_less_iff)

lemma neg_numeral_less_zero: "neg_numeral n < 0"
  by (simp only: neg_numeral_def neg_less_0_iff_less zero_less_numeral)

lemma neg_numeral_le_zero: "neg_numeral n \<le> 0"
  by (simp only: neg_numeral_def neg_le_0_iff_le zero_le_numeral)

lemma not_zero_less_neg_numeral: "\<not> 0 < neg_numeral n"
  by (simp only: not_less neg_numeral_le_zero)

lemma not_zero_le_neg_numeral: "\<not> 0 \<le> neg_numeral n"
  by (simp only: not_le neg_numeral_less_zero)

lemma neg_numeral_less_numeral: "neg_numeral m < numeral n"
  using neg_numeral_less_zero zero_less_numeral by (rule less_trans)

lemma neg_numeral_le_numeral: "neg_numeral m \<le> numeral n"
  by (simp only: less_imp_le neg_numeral_less_numeral)

lemma not_numeral_less_neg_numeral: "\<not> numeral m < neg_numeral n"
  by (simp only: not_less neg_numeral_le_numeral)

lemma not_numeral_le_neg_numeral: "\<not> numeral m \<le> neg_numeral n"
  by (simp only: not_le neg_numeral_less_numeral)
  
lemma neg_numeral_less_one: "neg_numeral m < 1"
  by (rule neg_numeral_less_numeral [of m One, unfolded numeral_One])

lemma neg_numeral_le_one: "neg_numeral m \<le> 1"
  by (rule neg_numeral_le_numeral [of m One, unfolded numeral_One])

lemma not_one_less_neg_numeral: "\<not> 1 < neg_numeral m"
  by (simp only: not_less neg_numeral_le_one)

lemma not_one_le_neg_numeral: "\<not> 1 \<le> neg_numeral m"
  by (simp only: not_le neg_numeral_less_one)

lemma sub_non_negative:
  "sub n m \<ge> 0 \<longleftrightarrow> n \<ge> m"
  by (simp only: sub_def le_diff_eq) simp

lemma sub_positive:
  "sub n m > 0 \<longleftrightarrow> n > m"
  by (simp only: sub_def less_diff_eq) simp

lemma sub_non_positive:
  "sub n m \<le> 0 \<longleftrightarrow> n \<le> m"
  by (simp only: sub_def diff_le_eq) simp

lemma sub_negative:
  "sub n m < 0 \<longleftrightarrow> n < m"
  by (simp only: sub_def diff_less_eq) simp

lemmas le_neg_numeral_simps [simp] =
  neg_numeral_le_iff
  neg_numeral_le_numeral not_numeral_le_neg_numeral
  neg_numeral_le_zero not_zero_le_neg_numeral
  neg_numeral_le_one not_one_le_neg_numeral

lemmas less_neg_numeral_simps [simp] =
  neg_numeral_less_iff
  neg_numeral_less_numeral not_numeral_less_neg_numeral
  neg_numeral_less_zero not_zero_less_neg_numeral
  neg_numeral_less_one not_one_less_neg_numeral

lemma abs_numeral [simp]: "abs (numeral n) = numeral n"
  by simp

lemma abs_neg_numeral [simp]: "abs (neg_numeral n) = numeral n"
  by (simp only: neg_numeral_def abs_minus_cancel abs_numeral)

end

subsubsection {*
  Natural numbers
*}

lemma Suc_numeral [simp]: "Suc (numeral n) = numeral (n + One)"
  unfolding numeral_plus_one [symmetric] by simp

lemma nat_number:
  "1 = Suc 0"
  "numeral One = Suc 0"
  "numeral (Bit0 n) = Suc (numeral (BitM n))"
  "numeral (Bit1 n) = Suc (numeral (Bit0 n))"
  by (simp_all add: numeral.simps BitM_plus_one)

subsubsection {*
  Structures with exponentiation
*}

context semiring_numeral
begin

lemma numeral_sqr: "numeral (sqr n) = numeral n * numeral n"
  by (simp add: sqr_conv_mult numeral_mult)

lemma numeral_pow: "numeral (pow m n) = numeral m ^ numeral n"
  by (induct n, simp_all add: numeral_class.numeral.simps
    power_add numeral_sqr numeral_mult)

lemma power_numeral [simp]: "numeral m ^ numeral n = numeral (pow m n)"
  by (rule numeral_pow [symmetric])

end

context semiring_1
begin

lemma power_zero_numeral [simp]: "(0::'a) ^ numeral n = 0"
  by (induct n, simp_all add: numeral_class.numeral.simps power_add)

end

context ring_1
begin

lemma power_minus_Bit0: "(- x) ^ numeral (Bit0 n) = x ^ numeral (Bit0 n)"
  by (induct n, simp_all add: numeral_class.numeral.simps power_add)

lemma power_minus_Bit1: "(- x) ^ numeral (Bit1 n) = - (x ^ numeral (Bit1 n))"
  by (simp only: nat_number(4) power_Suc power_minus_Bit0 mult_minus_left)

lemma power_neg_numeral_Bit0 [simp]:
  "neg_numeral m ^ numeral (Bit0 n) = numeral (pow m (Bit0 n))"
  by (simp only: neg_numeral_def power_minus_Bit0 power_numeral)

lemma power_neg_numeral_Bit1 [simp]:
  "neg_numeral m ^ numeral (Bit1 n) = neg_numeral (pow m (Bit1 n))"
  by (simp only: neg_numeral_def power_minus_Bit1 power_numeral pow.simps)

end

subsection {* Numeral equations as default simplification rules *}

declare (in numeral) numeral_One [simp]
declare (in numeral) numeral_plus_numeral [simp]
declare (in numeral) add_numeral_special [simp]
declare (in neg_numeral) add_neg_numeral_simps [simp]
declare (in neg_numeral) add_neg_numeral_special [simp]
declare (in neg_numeral) diff_numeral_simps [simp]
declare (in neg_numeral) diff_numeral_special [simp]
declare (in semiring_numeral) numeral_times_numeral [simp]
declare (in ring_1) mult_neg_numeral_simps [simp]

subsection {* Setting up simprocs *}

lemma numeral_reorient:
  "(numeral w = x) = (x = numeral w)"
  by auto

lemma mult_numeral_1: "Numeral1 * a = (a::'a::semiring_numeral)"
  by simp

lemma mult_numeral_1_right: "a * Numeral1 = (a::'a::semiring_numeral)"
  by simp

lemma divide_numeral_1: "a / Numeral1 = (a::'a::field)"
  by simp

lemma inverse_numeral_1:
  "inverse Numeral1 = (Numeral1::'a::division_ring)"
  by simp

text{*Theorem lists for the cancellation simprocs. The use of a numary
numeral for 1 reduces the number of special cases.*}

lemmas mult_1s =
  mult_numeral_1 mult_numeral_1_right 
  mult_minus1 mult_minus1_right


subsubsection {* Simplification of arithmetic operations on integer constants. *}

lemmas arith_special = (* already declared simp above *)
  add_numeral_special add_neg_numeral_special
  diff_numeral_special minus_one

(* rules already in simpset *)
lemmas arith_extra_simps =
  numeral_plus_numeral add_neg_numeral_simps add_0_left add_0_right
  minus_numeral minus_neg_numeral minus_zero minus_one
  diff_numeral_simps diff_0 diff_0_right
  numeral_times_numeral mult_neg_numeral_simps
  mult_zero_left mult_zero_right
  abs_numeral abs_neg_numeral

text {*
  For making a minimal simpset, one must include these default simprules.
  Also include @{text simp_thms}.
*}

lemmas arith_simps =
  add_num_simps mult_num_simps sub_num_simps
  BitM.simps dbl_simps dbl_inc_simps dbl_dec_simps
  abs_zero abs_one arith_extra_simps

text {* Simplification of relational operations *}

lemmas eq_numeral_extra =
  zero_neq_one one_neq_zero

lemmas rel_simps =
  le_num_simps less_num_simps eq_num_simps
  le_numeral_simps le_neg_numeral_simps le_numeral_extra
  less_numeral_simps less_neg_numeral_simps less_numeral_extra
  eq_numeral_simps eq_neg_numeral_simps eq_numeral_extra


subsubsection {* Simplification of arithmetic when nested to the right. *}

lemma add_numeral_left [simp]:
  "numeral v + (numeral w + z) = (numeral(v + w) + z)"
  by (simp_all add: add_assoc [symmetric])

lemma add_neg_numeral_left [simp]:
  "numeral v + (neg_numeral w + y) = (sub v w + y)"
  "neg_numeral v + (numeral w + y) = (sub w v + y)"
  "neg_numeral v + (neg_numeral w + y) = (neg_numeral(v + w) + y)"
  by (simp_all add: add_assoc [symmetric])

lemma mult_numeral_left [simp]:
  "numeral v * (numeral w * z) = (numeral(v * w) * z :: 'a::semiring_numeral)"
  "neg_numeral v * (numeral w * y) = (neg_numeral(v * w) * y :: 'b::ring_1)"
  "numeral v * (neg_numeral w * y) = (neg_numeral(v * w) * y :: 'b::ring_1)"
  "neg_numeral v * (neg_numeral w * y) = (numeral(v * w) * y :: 'b::ring_1)"
  by (simp_all add: mult_assoc [symmetric])

hide_const (open) One Bit0 Bit1 BitM inc pow sqr sub dbl dbl_inc dbl_dec

subsection {* code module namespace *}

code_modulename SML
  Numeral Arith

code_modulename OCaml
  Numeral Arith

code_modulename Haskell
  Numeral Arith

end
