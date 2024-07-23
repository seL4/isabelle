(*  Title:      HOL/Num.thy
    Author:     Florian Haftmann
    Author:     Brian Huffman
*)

section \<open>Binary Numerals\<close>

theory Num
  imports BNF_Least_Fixpoint Transfer
begin

subsection \<open>The \<open>num\<close> type\<close>

datatype num = One | Bit0 num | Bit1 num

text \<open>Increment function for type \<^typ>\<open>num\<close>\<close>

primrec inc :: "num \<Rightarrow> num"
  where
    "inc One = Bit0 One"
  | "inc (Bit0 x) = Bit1 x"
  | "inc (Bit1 x) = Bit0 (inc x)"

text \<open>Converting between type \<^typ>\<open>num\<close> and type \<^typ>\<open>nat\<close>\<close>

primrec nat_of_num :: "num \<Rightarrow> nat"
  where
    "nat_of_num One = Suc 0"
  | "nat_of_num (Bit0 x) = nat_of_num x + nat_of_num x"
  | "nat_of_num (Bit1 x) = Suc (nat_of_num x + nat_of_num x)"

primrec num_of_nat :: "nat \<Rightarrow> num"
  where
    "num_of_nat 0 = One"
  | "num_of_nat (Suc n) = (if 0 < n then inc (num_of_nat n) else One)"

lemma nat_of_num_pos: "0 < nat_of_num x"
  by (induct x) simp_all

lemma nat_of_num_neq_0: " nat_of_num x \<noteq> 0"
  by (induct x) simp_all

lemma nat_of_num_inc: "nat_of_num (inc x) = Suc (nat_of_num x)"
  by (induct x) simp_all

lemma num_of_nat_double: "0 < n \<Longrightarrow> num_of_nat (n + n) = Bit0 (num_of_nat n)"
  by (induct n) simp_all

text \<open>Type \<^typ>\<open>num\<close> is isomorphic to the strictly positive natural numbers.\<close>

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
    by (cases "nat_of_num x") (simp_all add: nat_of_num_neq_0)
  have "P (num_of_nat (Suc n))"
  proof (induct n)
    case 0
    from One show ?case by simp
  next
    case (Suc n)
    then have "P (inc (num_of_nat (Suc n)))" by (rule inc)
    then show "P (num_of_nat (Suc (Suc n)))" by simp
  qed
  with n show "P x"
    by (simp add: nat_of_num_inverse)
qed

text \<open>
  From now on, there are two possible models for \<^typ>\<open>num\<close>: as positive
  naturals (rule \<open>num_induct\<close>) and as digit representation (rules
  \<open>num.induct\<close>, \<open>num.cases\<close>).
\<close>


subsection \<open>Numeral operations\<close>

instantiation num :: "{plus,times,linorder}"
begin

definition [code del]: "m + n = num_of_nat (nat_of_num m + nat_of_num n)"

definition [code del]: "m * n = num_of_nat (nat_of_num m * nat_of_num n)"

definition [code del]: "m \<le> n \<longleftrightarrow> nat_of_num m \<le> nat_of_num n"

definition [code del]: "m < n \<longleftrightarrow> nat_of_num m < nat_of_num n"

instance
  by standard (auto simp add: less_num_def less_eq_num_def num_eq_iff)

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
  by (simp_all add: num_eq_iff nat_of_num_add nat_of_num_mult distrib_right distrib_left)

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

lemma le_num_One_iff: "x \<le> num.One \<longleftrightarrow> x = num.One"
  by (simp add: antisym_conv)

text \<open>Rules using \<open>One\<close> and \<open>inc\<close> as constructors.\<close>

lemma add_One: "x + One = inc x"
  by (simp add: num_eq_iff nat_of_num_add nat_of_num_inc)

lemma add_One_commute: "One + n = n + One"
  by (induct n) simp_all

lemma add_inc: "x + inc y = inc (x + y)"
  by (simp add: num_eq_iff nat_of_num_add nat_of_num_inc)

lemma mult_inc: "x * inc y = x * y + x"
  by (simp add: num_eq_iff nat_of_num_mult nat_of_num_add nat_of_num_inc)

text \<open>The \<^const>\<open>num_of_nat\<close> conversion.\<close>

lemma num_of_nat_One: "n \<le> 1 \<Longrightarrow> num_of_nat n = One"
  by (cases n) simp_all

lemma num_of_nat_plus_distrib:
  "0 < m \<Longrightarrow> 0 < n \<Longrightarrow> num_of_nat (m + n) = num_of_nat m + num_of_nat n"
  by (induct n) (auto simp add: add_One add_One_commute add_inc)

text \<open>A double-and-decrement function.\<close>

primrec BitM :: "num \<Rightarrow> num"
  where
    "BitM One = One"
  | "BitM (Bit0 n) = Bit1 (BitM n)"
  | "BitM (Bit1 n) = Bit1 (Bit0 n)"

lemma BitM_plus_one: "BitM n + One = Bit0 n"
  by (induct n) simp_all

lemma one_plus_BitM: "One + BitM n = Bit0 n"
  unfolding add_One_commute BitM_plus_one ..

lemma BitM_inc_eq:
  \<open>Num.BitM (Num.inc n) = Num.Bit1 n\<close>
  by (induction n) simp_all

lemma inc_BitM_eq:
  \<open>Num.inc (Num.BitM n) = num.Bit0 n\<close>
  by (simp add: BitM_plus_one[symmetric] add_One)

text \<open>Squaring and exponentiation.\<close>

primrec sqr :: "num \<Rightarrow> num"
  where
    "sqr One = One"
  | "sqr (Bit0 n) = Bit0 (Bit0 (sqr n))"
  | "sqr (Bit1 n) = Bit1 (Bit0 (sqr n + n))"

primrec pow :: "num \<Rightarrow> num \<Rightarrow> num"
  where
    "pow x One = x"
  | "pow x (Bit0 y) = sqr (pow x y)"
  | "pow x (Bit1 y) = sqr (pow x y) * x"

lemma nat_of_num_sqr: "nat_of_num (sqr x) = nat_of_num x * nat_of_num x"
  by (induct x) (simp_all add: algebra_simps nat_of_num_add)

lemma sqr_conv_mult: "sqr x = x * x"
  by (simp add: num_eq_iff nat_of_num_sqr nat_of_num_mult)

lemma num_double [simp]:
  "num.Bit0 num.One * n = num.Bit0 n"
  by (simp add: num_eq_iff nat_of_num_mult)


subsection \<open>Binary numerals\<close>

text \<open>
  We embed binary representations into a generic algebraic
  structure using \<open>numeral\<close>.
\<close>

class numeral = one + semigroup_add
begin

primrec numeral :: "num \<Rightarrow> 'a"
  where
    numeral_One: "numeral One = 1"
  | numeral_Bit0: "numeral (Bit0 n) = numeral n + numeral n"
  | numeral_Bit1: "numeral (Bit1 n) = numeral n + numeral n + 1"

lemma numeral_code [code]:
  "numeral One = 1"
  "numeral (Bit0 n) = (let m = numeral n in m + m)"
  "numeral (Bit1 n) = (let m = numeral n in m + m + 1)"
  by (simp_all add: Let_def)

lemma one_plus_numeral_commute: "1 + numeral x = numeral x + 1"
proof (induct x)
  case One
  then show ?case by simp
next
  case Bit0
  then show ?case by (simp add: add.assoc [symmetric]) (simp add: add.assoc)
next
  case Bit1
  then show ?case by (simp add: add.assoc [symmetric]) (simp add: add.assoc)
qed

lemma numeral_inc: "numeral (inc x) = numeral x + 1"
proof (induct x)
  case One
  then show ?case by simp
next
  case Bit0
  then show ?case by simp
next
  case (Bit1 x)
  have "numeral x + (1 + numeral x) + 1 = numeral x + (numeral x + 1) + 1"
    by (simp only: one_plus_numeral_commute)
  with Bit1 show ?case
    by (simp add: add.assoc)
qed

declare numeral.simps [simp del]

abbreviation "Numeral1 \<equiv> numeral One"

declare numeral_One [code_post]

end

text \<open>Numeral syntax.\<close>

syntax
  "_Numeral" :: "num_const \<Rightarrow> 'a"    ("_")

ML_file \<open>Tools/numeral.ML\<close>

parse_translation \<open>
  let
    fun numeral_tr [(c as Const (\<^syntax_const>\<open>_constrain\<close>, _)) $ t $ u] =
          c $ numeral_tr [t] $ u
      | numeral_tr [Const (num, _)] =
          (Numeral.mk_number_syntax o #value o Lexicon.read_num) num
      | numeral_tr ts = raise TERM ("numeral_tr", ts);
  in [(\<^syntax_const>\<open>_Numeral\<close>, K numeral_tr)] end
\<close>

typed_print_translation \<open>
  let
    fun num_tr' ctxt T [n] =
      let
        val k = Numeral.dest_num_syntax n;
        val t' =
          Syntax.const \<^syntax_const>\<open>_Numeral\<close> $
            Syntax.free (string_of_int k);
      in
        (case T of
          Type (\<^type_name>\<open>fun\<close>, [_, T']) =>
            if Printer.type_emphasis ctxt T' then
              Syntax.const \<^syntax_const>\<open>_constrain\<close> $ t' $
                Syntax_Phases.term_of_typ ctxt T'
            else t'
        | _ => if T = dummyT then t' else raise Match)
      end;
  in
   [(\<^const_syntax>\<open>numeral\<close>, num_tr')]
  end
\<close>


subsection \<open>Class-specific numeral rules\<close>

text \<open>\<^const>\<open>numeral\<close> is a morphism.\<close>


subsubsection \<open>Structures with addition: class \<open>numeral\<close>\<close>

context numeral
begin

lemma numeral_add: "numeral (m + n) = numeral m + numeral n"
  by (induct n rule: num_induct)
    (simp_all only: numeral_One add_One add_inc numeral_inc add.assoc)

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


subsubsection \<open>Structures with negation: class \<open>neg_numeral\<close>\<close>

class neg_numeral = numeral + group_add
begin

lemma uminus_numeral_One: "- Numeral1 = - 1"
  by (simp add: numeral_One)

text \<open>Numerals form an abelian subgroup.\<close>

inductive is_num :: "'a \<Rightarrow> bool"
  where
    "is_num 1"
  | "is_num x \<Longrightarrow> is_num (- x)"
  | "is_num x \<Longrightarrow> is_num y \<Longrightarrow> is_num (x + y)"

lemma is_num_numeral: "is_num (numeral k)"
  by (induct k) (simp_all add: numeral.simps is_num.intros)

lemma is_num_add_commute: "is_num x \<Longrightarrow> is_num y \<Longrightarrow> x + y = y + x"
proof(induction x rule: is_num.induct)
  case 1
  then show ?case
  proof (induction y rule: is_num.induct)
    case 1
    then show ?case by simp
  next
    case (2 y)
    then have "y + (1 + - y) + y = y + (- y + 1) + y"
      by (simp add: add.assoc)
    then have "y + (1 + - y) = y + (- y + 1)"
      by simp
    then show ?case
      by (rule add_left_imp_eq[of y])
  next
    case (3 x y)
    then have "1 + (x + y) = x + 1 + y"
      by (simp add: add.assoc [symmetric])
    then show ?case using 3
      by (simp add: add.assoc)
  qed
next
  case (2 x)
  then have "x + (- x + y) + x = x + (y + - x) + x"
    by (simp add: add.assoc)
  then have "x + (- x + y) = x + (y + - x)"
    by simp
  then show ?case
    by (rule add_left_imp_eq[of x])
next
  case (3 x z)
  moreover have "x + (y + z) = (x + y) + z"
    by (simp add: add.assoc[symmetric])
  ultimately show ?case 
    by (simp add: add.assoc)
qed

lemma is_num_add_left_commute: "is_num x \<Longrightarrow> is_num y \<Longrightarrow> x + (y + z) = y + (x + z)"
  by (simp only: add.assoc [symmetric] is_num_add_commute)

lemmas is_num_normalize =
  add.assoc is_num_add_commute is_num_add_left_commute
  is_num.intros is_num_numeral
  minus_add

definition dbl :: "'a \<Rightarrow> 'a"
  where "dbl x = x + x"

definition dbl_inc :: "'a \<Rightarrow> 'a"
  where "dbl_inc x = x + x + 1"

definition dbl_dec :: "'a \<Rightarrow> 'a"
  where "dbl_dec x = x + x - 1"

definition sub :: "num \<Rightarrow> num \<Rightarrow> 'a"
  where "sub k l = numeral k - numeral l"

lemma numeral_BitM: "numeral (BitM n) = numeral (Bit0 n) - 1"
  by (simp only: BitM_plus_one [symmetric] numeral_add numeral_One eq_diff_eq)

lemma sub_inc_One_eq:
  \<open>Num.sub (Num.inc n) num.One = numeral n\<close>
  by (simp_all add: sub_def diff_eq_eq numeral_inc numeral.numeral_One)

lemma dbl_simps [simp]:
  "dbl (- numeral k) = - dbl (numeral k)"
  "dbl 0 = 0"
  "dbl 1 = 2"
  "dbl (- 1) = - 2"
  "dbl (numeral k) = numeral (Bit0 k)"
  by (simp_all add: dbl_def numeral.simps minus_add)

lemma dbl_inc_simps [simp]:
  "dbl_inc (- numeral k) = - dbl_dec (numeral k)"
  "dbl_inc 0 = 1"
  "dbl_inc 1 = 3"
  "dbl_inc (- 1) = - 1"
  "dbl_inc (numeral k) = numeral (Bit1 k)"
  by (simp_all add: dbl_inc_def dbl_dec_def numeral.simps numeral_BitM is_num_normalize algebra_simps
      del: add_uminus_conv_diff)

lemma dbl_dec_simps [simp]:
  "dbl_dec (- numeral k) = - dbl_inc (numeral k)"
  "dbl_dec 0 = - 1"
  "dbl_dec 1 = 1"
  "dbl_dec (- 1) = - 3"
  "dbl_dec (numeral k) = numeral (BitM k)"
  by (simp_all add: dbl_dec_def dbl_inc_def numeral.simps numeral_BitM is_num_normalize)

lemma sub_num_simps [simp]:
  "sub One One = 0"
  "sub One (Bit0 l) = - numeral (BitM l)"
  "sub One (Bit1 l) = - numeral (Bit0 l)"
  "sub (Bit0 k) One = numeral (BitM k)"
  "sub (Bit1 k) One = numeral (Bit0 k)"
  "sub (Bit0 k) (Bit0 l) = dbl (sub k l)"
  "sub (Bit0 k) (Bit1 l) = dbl_dec (sub k l)"
  "sub (Bit1 k) (Bit0 l) = dbl_inc (sub k l)"
  "sub (Bit1 k) (Bit1 l) = dbl (sub k l)"
  by (simp_all add: dbl_def dbl_dec_def dbl_inc_def sub_def numeral.simps
    numeral_BitM is_num_normalize del: add_uminus_conv_diff add: diff_conv_add_uminus)

lemma add_neg_numeral_simps:
  "numeral m + - numeral n = sub m n"
  "- numeral m + numeral n = sub n m"
  "- numeral m + - numeral n = - (numeral m + numeral n)"
  by (simp_all add: sub_def numeral_add numeral.simps is_num_normalize
      del: add_uminus_conv_diff add: diff_conv_add_uminus)

lemma add_neg_numeral_special:
  "1 + - numeral m = sub One m"
  "- numeral m + 1 = sub One m"
  "numeral m + - 1 = sub m One"
  "- 1 + numeral n = sub n One"
  "- 1 + - numeral n = - numeral (inc n)"
  "- numeral m + - 1 = - numeral (inc m)"
  "1 + - 1 = 0"
  "- 1 + 1 = 0"
  "- 1 + - 1 = - 2"
  by (simp_all add: sub_def numeral_add numeral.simps is_num_normalize right_minus numeral_inc
      del: add_uminus_conv_diff add: diff_conv_add_uminus)

lemma diff_numeral_simps:
  "numeral m - numeral n = sub m n"
  "numeral m - - numeral n = numeral (m + n)"
  "- numeral m - numeral n = - numeral (m + n)"
  "- numeral m - - numeral n = sub n m"
  by (simp_all add: sub_def numeral_add numeral.simps is_num_normalize
      del: add_uminus_conv_diff add: diff_conv_add_uminus)

lemma diff_numeral_special:
  "1 - numeral n = sub One n"
  "numeral m - 1 = sub m One"
  "1 - - numeral n = numeral (One + n)"
  "- numeral m - 1 = - numeral (m + One)"
  "- 1 - numeral n = - numeral (inc n)"
  "numeral m - - 1 = numeral (inc m)"
  "- 1 - - numeral n = sub n One"
  "- numeral m - - 1 = sub One m"
  "1 - 1 = 0"
  "- 1 - 1 = - 2"
  "1 - - 1 = 2"
  "- 1 - - 1 = 0"
  by (simp_all add: sub_def numeral_add numeral.simps is_num_normalize numeral_inc
      del: add_uminus_conv_diff add: diff_conv_add_uminus)

end


subsubsection \<open>Structures with multiplication: class \<open>semiring_numeral\<close>\<close>

class semiring_numeral = semiring + monoid_mult
begin

subclass numeral ..

lemma numeral_mult: "numeral (m * n) = numeral m * numeral n"
  by (induct n rule: num_induct)
    (simp_all add: numeral_One mult_inc numeral_inc numeral_add distrib_left)

lemma numeral_times_numeral: "numeral m * numeral n = numeral (m * n)"
  by (rule numeral_mult [symmetric])

lemma mult_2: "2 * z = z + z"
  by (simp add: one_add_one [symmetric] distrib_right)

lemma mult_2_right: "z * 2 = z + z"
  by (simp add: one_add_one [symmetric] distrib_left)

lemma left_add_twice:
  "a + (a + b) = 2 * a + b"
  by (simp add: mult_2 ac_simps)

lemma numeral_Bit0_eq_double:
  \<open>numeral (num.Bit0 n) = 2 * numeral n\<close>
  by (simp add: mult_2) (simp add: numeral_Bit0)

lemma numeral_Bit1_eq_inc_double:
  \<open>numeral (num.Bit1 n) = 2 * numeral n + 1\<close>
  by (simp add: mult_2) (simp add: numeral_Bit1)

end


subsubsection \<open>Structures with a zero: class \<open>semiring_1\<close>\<close>

context semiring_1
begin

subclass semiring_numeral ..

lemma of_nat_numeral [simp]: "of_nat (numeral n) = numeral n"
  by (induct n) (simp_all only: numeral.simps numeral_class.numeral.simps of_nat_add of_nat_1)

end

lemma nat_of_num_numeral [code_abbrev]: "nat_of_num = numeral"
proof
  fix n
  have "numeral n = nat_of_num n"
    by (induct n) (simp_all add: numeral.simps)
  then show "nat_of_num n = numeral n"
    by simp
qed

lemma nat_of_num_code [code]:
  "nat_of_num One = 1"
  "nat_of_num (Bit0 n) = (let m = nat_of_num n in m + m)"
  "nat_of_num (Bit1 n) = (let m = nat_of_num n in Suc (m + m))"
  by (simp_all add: Let_def)


subsubsection \<open>Equality: class \<open>semiring_char_0\<close>\<close>

context semiring_char_0
begin

lemma numeral_eq_iff: "numeral m = numeral n \<longleftrightarrow> m = n"
  by (simp only: of_nat_numeral [symmetric] nat_of_num_numeral [symmetric]
    of_nat_eq_iff num_eq_iff)

lemma numeral_eq_one_iff: "numeral n = 1 \<longleftrightarrow> n = One"
  by (rule numeral_eq_iff [of n One, unfolded numeral_One])

lemma one_eq_numeral_iff: "1 = numeral n \<longleftrightarrow> One = n"
  by (rule numeral_eq_iff [of One n, unfolded numeral_One])

lemma numeral_neq_zero: "numeral n \<noteq> 0"
  by (simp add: of_nat_numeral [symmetric] nat_of_num_numeral [symmetric] nat_of_num_pos)

lemma zero_neq_numeral: "0 \<noteq> numeral n"
  unfolding eq_commute [of 0] by (rule numeral_neq_zero)

lemmas eq_numeral_simps [simp] =
  numeral_eq_iff
  numeral_eq_one_iff
  one_eq_numeral_iff
  numeral_neq_zero
  zero_neq_numeral

end


subsubsection \<open>Comparisons: class \<open>linordered_nonzero_semiring\<close>\<close>

context linordered_nonzero_semiring
begin

lemma numeral_le_iff: "numeral m \<le> numeral n \<longleftrightarrow> m \<le> n"
proof -
  have "of_nat (numeral m) \<le> of_nat (numeral n) \<longleftrightarrow> m \<le> n"
    by (simp only: less_eq_num_def nat_of_num_numeral of_nat_le_iff)
  then show ?thesis by simp
qed

lemma one_le_numeral: "1 \<le> numeral n"
  using numeral_le_iff [of num.One n] by (simp add: numeral_One)

lemma numeral_le_one_iff: "numeral n \<le> 1 \<longleftrightarrow> n \<le> num.One"
  using numeral_le_iff [of n num.One] by (simp add: numeral_One)

lemma numeral_less_iff: "numeral m < numeral n \<longleftrightarrow> m < n"
proof -
  have "of_nat (numeral m) < of_nat (numeral n) \<longleftrightarrow> m < n"
    unfolding less_num_def nat_of_num_numeral of_nat_less_iff ..
  then show ?thesis by simp
qed

lemma not_numeral_less_one: "\<not> numeral n < 1"
  using numeral_less_iff [of n num.One] by (simp add: numeral_One)

lemma one_less_numeral_iff: "1 < numeral n \<longleftrightarrow> num.One < n"
  using numeral_less_iff [of num.One n] by (simp add: numeral_One)

lemma zero_le_numeral: "0 \<le> numeral n"
  using dual_order.trans one_le_numeral zero_le_one by blast

lemma zero_less_numeral: "0 < numeral n"
  using less_linear not_numeral_less_one order.strict_trans zero_less_one by blast

lemma not_numeral_le_zero: "\<not> numeral n \<le> 0"
  by (simp add: not_le zero_less_numeral)

lemma not_numeral_less_zero: "\<not> numeral n < 0"
  by (simp add: not_less zero_le_numeral)

lemma one_of_nat_le_iff [simp]: "1 \<le> of_nat k \<longleftrightarrow> 1 \<le> k"
  using of_nat_le_iff [of 1] by simp

lemma numeral_nat_le_iff [simp]: "numeral n \<le> of_nat k \<longleftrightarrow> numeral n \<le> k"
  using of_nat_le_iff [of "numeral n"] by simp

lemma of_nat_le_1_iff [simp]: "of_nat k \<le> 1 \<longleftrightarrow> k \<le> 1"
  using of_nat_le_iff [of _ 1] by simp

lemma of_nat_le_numeral_iff [simp]: "of_nat k \<le> numeral n \<longleftrightarrow> k \<le> numeral n"
  using of_nat_le_iff [of _ "numeral n"] by simp

lemma one_of_nat_less_iff [simp]: "1 < of_nat k \<longleftrightarrow> 1 < k"
  using of_nat_less_iff [of 1] by simp

lemma numeral_nat_less_iff [simp]: "numeral n < of_nat k \<longleftrightarrow> numeral n < k"
  using of_nat_less_iff [of "numeral n"] by simp

lemma of_nat_less_1_iff [simp]: "of_nat k < 1 \<longleftrightarrow> k < 1"
  using of_nat_less_iff [of _ 1] by simp

lemma of_nat_less_numeral_iff [simp]: "of_nat k < numeral n \<longleftrightarrow> k < numeral n"
  using of_nat_less_iff [of _ "numeral n"] by simp

lemma of_nat_eq_numeral_iff [simp]: "of_nat k = numeral n \<longleftrightarrow> k = numeral n"
  using of_nat_eq_iff [of _ "numeral n"] by simp

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

lemma min_0_1 [simp]:
  fixes min' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  defines "min' \<equiv> min"
  shows
    "min' 0 1 = 0"
    "min' 1 0 = 0"
    "min' 0 (numeral x) = 0"
    "min' (numeral x) 0 = 0"
    "min' 1 (numeral x) = 1"
    "min' (numeral x) 1 = 1"
  by (simp_all add: min'_def min_def le_num_One_iff)

lemma max_0_1 [simp]:
  fixes max' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  defines "max' \<equiv> max"
  shows
    "max' 0 1 = 1"
    "max' 1 0 = 1"
    "max' 0 (numeral x) = numeral x"
    "max' (numeral x) 0 = numeral x"
    "max' 1 (numeral x) = numeral x"
    "max' (numeral x) 1 = numeral x"
  by (simp_all add: max'_def max_def le_num_One_iff)

end

text \<open>Unfold \<open>min\<close> and \<open>max\<close> on numerals.\<close>

lemmas max_number_of [simp] =
  max_def [of "numeral u" "numeral v"]
  max_def [of "numeral u" "- numeral v"]
  max_def [of "- numeral u" "numeral v"]
  max_def [of "- numeral u" "- numeral v"] for u v

lemmas min_number_of [simp] =
  min_def [of "numeral u" "numeral v"]
  min_def [of "numeral u" "- numeral v"]
  min_def [of "- numeral u" "numeral v"]
  min_def [of "- numeral u" "- numeral v"] for u v


subsubsection \<open>Multiplication and negation: class \<open>ring_1\<close>\<close>

context ring_1
begin

subclass neg_numeral ..

lemma mult_neg_numeral_simps:
  "- numeral m * - numeral n = numeral (m * n)"
  "- numeral m * numeral n = - numeral (m * n)"
  "numeral m * - numeral n = - numeral (m * n)"
  by (simp_all only: mult_minus_left mult_minus_right minus_minus numeral_mult)

lemma mult_minus1 [simp]: "- 1 * z = - z"
  by (simp add: numeral.simps)

lemma mult_minus1_right [simp]: "z * - 1 = - z"
  by (simp add: numeral.simps)

lemma minus_sub_one_diff_one [simp]:
  \<open>- sub m One - 1 = - numeral m\<close>
proof -
  have \<open>sub m One + 1 = numeral m\<close>
    by (simp flip: eq_diff_eq add: diff_numeral_special)
  then have \<open>- (sub m One + 1) = - numeral m\<close>
    by simp
  then show ?thesis
    by simp
qed

end


subsubsection \<open>Equality using \<open>iszero\<close> for rings with non-zero characteristic\<close>

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

lemma not_iszero_neg_1 [simp]: "\<not> iszero (- 1)"
  by (simp add: iszero_def)

lemma not_iszero_neg_Numeral1: "\<not> iszero (- Numeral1)"
  by (simp add: numeral_One)

lemma iszero_neg_numeral [simp]: "iszero (- numeral w) \<longleftrightarrow> iszero (numeral w)"
  unfolding iszero_def by (rule neg_equal_0_iff_equal)

lemma eq_iff_iszero_diff: "x = y \<longleftrightarrow> iszero (x - y)"
  unfolding iszero_def by (rule eq_iff_diff_eq_0)

text \<open>
  The \<open>eq_numeral_iff_iszero\<close> lemmas are not declared \<open>[simp]\<close> by default,
  because for rings of characteristic zero, better simp rules are possible.
  For a type like integers mod \<open>n\<close>, type-instantiated versions of these rules
  should be added to the simplifier, along with a type-specific rule for
  deciding propositions of the form \<open>iszero (numeral w)\<close>.

  bh: Maybe it would not be so bad to just declare these as simp rules anyway?
  I should test whether these rules take precedence over the \<open>ring_char_0\<close>
  rules in the simplifier.
\<close>

lemma eq_numeral_iff_iszero:
  "numeral x = numeral y \<longleftrightarrow> iszero (sub x y)"
  "numeral x = - numeral y \<longleftrightarrow> iszero (numeral (x + y))"
  "- numeral x = numeral y \<longleftrightarrow> iszero (numeral (x + y))"
  "- numeral x = - numeral y \<longleftrightarrow> iszero (sub y x)"
  "numeral x = 1 \<longleftrightarrow> iszero (sub x One)"
  "1 = numeral y \<longleftrightarrow> iszero (sub One y)"
  "- numeral x = 1 \<longleftrightarrow> iszero (numeral (x + One))"
  "1 = - numeral y \<longleftrightarrow> iszero (numeral (One + y))"
  "numeral x = 0 \<longleftrightarrow> iszero (numeral x)"
  "0 = numeral y \<longleftrightarrow> iszero (numeral y)"
  "- numeral x = 0 \<longleftrightarrow> iszero (numeral x)"
  "0 = - numeral y \<longleftrightarrow> iszero (numeral y)"
  unfolding eq_iff_iszero_diff diff_numeral_simps diff_numeral_special
  by simp_all

end


subsubsection \<open>Equality and negation: class \<open>ring_char_0\<close>\<close>

context ring_char_0
begin

lemma not_iszero_numeral [simp]: "\<not> iszero (numeral w)"
  by (simp add: iszero_def)

lemma neg_numeral_eq_iff: "- numeral m = - numeral n \<longleftrightarrow> m = n"
  by simp

lemma numeral_neq_neg_numeral: "numeral m \<noteq> - numeral n"
  by (simp add: eq_neg_iff_add_eq_0 numeral_plus_numeral)

lemma neg_numeral_neq_numeral: "- numeral m \<noteq> numeral n"
  by (rule numeral_neq_neg_numeral [symmetric])

lemma zero_neq_neg_numeral: "0 \<noteq> - numeral n"
  by simp

lemma neg_numeral_neq_zero: "- numeral n \<noteq> 0"
  by simp

lemma one_neq_neg_numeral: "1 \<noteq> - numeral n"
  using numeral_neq_neg_numeral [of One n] by (simp add: numeral_One)

lemma neg_numeral_neq_one: "- numeral n \<noteq> 1"
  using neg_numeral_neq_numeral [of n One] by (simp add: numeral_One)

lemma neg_one_neq_numeral: "- 1 \<noteq> numeral n"
  using neg_numeral_neq_numeral [of One n] by (simp add: numeral_One)

lemma numeral_neq_neg_one: "numeral n \<noteq> - 1"
  using numeral_neq_neg_numeral [of n One] by (simp add: numeral_One)

lemma neg_one_eq_numeral_iff: "- 1 = - numeral n \<longleftrightarrow> n = One"
  using neg_numeral_eq_iff [of One n] by (auto simp add: numeral_One)

lemma numeral_eq_neg_one_iff: "- numeral n = - 1 \<longleftrightarrow> n = One"
  using neg_numeral_eq_iff [of n One] by (auto simp add: numeral_One)

lemma neg_one_neq_zero: "- 1 \<noteq> 0"
  by simp

lemma zero_neq_neg_one: "0 \<noteq> - 1"
  by simp

lemma neg_one_neq_one: "- 1 \<noteq> 1"
  using neg_numeral_neq_numeral [of One One] by (simp only: numeral_One not_False_eq_True)

lemma one_neq_neg_one: "1 \<noteq> - 1"
  using numeral_neq_neg_numeral [of One One] by (simp only: numeral_One not_False_eq_True)

lemmas eq_neg_numeral_simps [simp] =
  neg_numeral_eq_iff
  numeral_neq_neg_numeral neg_numeral_neq_numeral
  one_neq_neg_numeral neg_numeral_neq_one
  zero_neq_neg_numeral neg_numeral_neq_zero
  neg_one_neq_numeral numeral_neq_neg_one
  neg_one_eq_numeral_iff numeral_eq_neg_one_iff
  neg_one_neq_zero zero_neq_neg_one
  neg_one_neq_one one_neq_neg_one

end


subsubsection \<open>Structures with negation and order: class \<open>linordered_idom\<close>\<close>

context linordered_idom
begin

subclass ring_char_0 ..

lemma neg_numeral_le_iff: "- numeral m \<le> - numeral n \<longleftrightarrow> n \<le> m"
  by (simp only: neg_le_iff_le numeral_le_iff)

lemma neg_numeral_less_iff: "- numeral m < - numeral n \<longleftrightarrow> n < m"
  by (simp only: neg_less_iff_less numeral_less_iff)

lemma neg_numeral_less_zero: "- numeral n < 0"
  by (simp only: neg_less_0_iff_less zero_less_numeral)

lemma neg_numeral_le_zero: "- numeral n \<le> 0"
  by (simp only: neg_le_0_iff_le zero_le_numeral)

lemma not_zero_less_neg_numeral: "\<not> 0 < - numeral n"
  by (simp only: not_less neg_numeral_le_zero)

lemma not_zero_le_neg_numeral: "\<not> 0 \<le> - numeral n"
  by (simp only: not_le neg_numeral_less_zero)

lemma neg_numeral_less_numeral: "- numeral m < numeral n"
  using neg_numeral_less_zero zero_less_numeral by (rule less_trans)

lemma neg_numeral_le_numeral: "- numeral m \<le> numeral n"
  by (simp only: less_imp_le neg_numeral_less_numeral)

lemma not_numeral_less_neg_numeral: "\<not> numeral m < - numeral n"
  by (simp only: not_less neg_numeral_le_numeral)

lemma not_numeral_le_neg_numeral: "\<not> numeral m \<le> - numeral n"
  by (simp only: not_le neg_numeral_less_numeral)

lemma neg_numeral_less_one: "- numeral m < 1"
  by (rule neg_numeral_less_numeral [of m One, unfolded numeral_One])

lemma neg_numeral_le_one: "- numeral m \<le> 1"
  by (rule neg_numeral_le_numeral [of m One, unfolded numeral_One])

lemma not_one_less_neg_numeral: "\<not> 1 < - numeral m"
  by (simp only: not_less neg_numeral_le_one)

lemma not_one_le_neg_numeral: "\<not> 1 \<le> - numeral m"
  by (simp only: not_le neg_numeral_less_one)

lemma not_numeral_less_neg_one: "\<not> numeral m < - 1"
  using not_numeral_less_neg_numeral [of m One] by (simp add: numeral_One)

lemma not_numeral_le_neg_one: "\<not> numeral m \<le> - 1"
  using not_numeral_le_neg_numeral [of m One] by (simp add: numeral_One)

lemma neg_one_less_numeral: "- 1 < numeral m"
  using neg_numeral_less_numeral [of One m] by (simp add: numeral_One)

lemma neg_one_le_numeral: "- 1 \<le> numeral m"
  using neg_numeral_le_numeral [of One m] by (simp add: numeral_One)

lemma neg_numeral_less_neg_one_iff: "- numeral m < - 1 \<longleftrightarrow> m \<noteq> One"
  by (cases m) simp_all

lemma neg_numeral_le_neg_one: "- numeral m \<le> - 1"
  by simp

lemma not_neg_one_less_neg_numeral: "\<not> - 1 < - numeral m"
  by simp

lemma not_neg_one_le_neg_numeral_iff: "\<not> - 1 \<le> - numeral m \<longleftrightarrow> m \<noteq> One"
  by (cases m) simp_all

lemma sub_non_negative: "sub n m \<ge> 0 \<longleftrightarrow> n \<ge> m"
  by (simp only: sub_def le_diff_eq) simp

lemma sub_positive: "sub n m > 0 \<longleftrightarrow> n > m"
  by (simp only: sub_def less_diff_eq) simp

lemma sub_non_positive: "sub n m \<le> 0 \<longleftrightarrow> n \<le> m"
  by (simp only: sub_def diff_le_eq) simp

lemma sub_negative: "sub n m < 0 \<longleftrightarrow> n < m"
  by (simp only: sub_def diff_less_eq) simp

lemmas le_neg_numeral_simps [simp] =
  neg_numeral_le_iff
  neg_numeral_le_numeral not_numeral_le_neg_numeral
  neg_numeral_le_zero not_zero_le_neg_numeral
  neg_numeral_le_one not_one_le_neg_numeral
  neg_one_le_numeral not_numeral_le_neg_one
  neg_numeral_le_neg_one not_neg_one_le_neg_numeral_iff

lemma le_minus_one_simps [simp]:
  "- 1 \<le> 0"
  "- 1 \<le> 1"
  "\<not> 0 \<le> - 1"
  "\<not> 1 \<le> - 1"
  by simp_all

lemmas less_neg_numeral_simps [simp] =
  neg_numeral_less_iff
  neg_numeral_less_numeral not_numeral_less_neg_numeral
  neg_numeral_less_zero not_zero_less_neg_numeral
  neg_numeral_less_one not_one_less_neg_numeral
  neg_one_less_numeral not_numeral_less_neg_one
  neg_numeral_less_neg_one_iff not_neg_one_less_neg_numeral

lemma less_minus_one_simps [simp]:
  "- 1 < 0"
  "- 1 < 1"
  "\<not> 0 < - 1"
  "\<not> 1 < - 1"
  by (simp_all add: less_le)

lemma abs_numeral [simp]: "\<bar>numeral n\<bar> = numeral n"
  by simp

lemma abs_neg_numeral [simp]: "\<bar>- numeral n\<bar> = numeral n"
  by (simp only: abs_minus_cancel abs_numeral)

lemma abs_neg_one [simp]: "\<bar>- 1\<bar> = 1"
  by simp

end


subsubsection \<open>Natural numbers\<close>

lemma numeral_num_of_nat:
  "numeral (num_of_nat n) = n" if "n > 0"
  using that nat_of_num_numeral num_of_nat_inverse by simp

lemma Suc_1 [simp]: "Suc 1 = 2"
  unfolding Suc_eq_plus1 by (rule one_add_one)

lemma Suc_numeral [simp]: "Suc (numeral n) = numeral (n + One)"
  unfolding Suc_eq_plus1 by (rule numeral_plus_one)

definition pred_numeral :: "num \<Rightarrow> nat"
  where "pred_numeral k = numeral k - 1"

declare [[code drop: pred_numeral]]

lemma numeral_eq_Suc: "numeral k = Suc (pred_numeral k)"
  by (simp add: pred_numeral_def)

lemma eval_nat_numeral:
  "numeral One = Suc 0"
  "numeral (Bit0 n) = Suc (numeral (BitM n))"
  "numeral (Bit1 n) = Suc (numeral (Bit0 n))"
  by (simp_all add: numeral.simps BitM_plus_one)

lemma pred_numeral_simps [simp]:
  "pred_numeral One = 0"
  "pred_numeral (Bit0 k) = numeral (BitM k)"
  "pred_numeral (Bit1 k) = numeral (Bit0 k)"
  by (simp_all only: pred_numeral_def eval_nat_numeral diff_Suc_Suc diff_0)

lemma pred_numeral_inc [simp]:
  "pred_numeral (Num.inc k) = numeral k"
  by (simp only: pred_numeral_def numeral_inc diff_add_inverse2)

lemma numeral_2_eq_2: "2 = Suc (Suc 0)"
  by (simp add: eval_nat_numeral)

lemma numeral_3_eq_3: "3 = Suc (Suc (Suc 0))"
  by (simp add: eval_nat_numeral)

lemma numeral_1_eq_Suc_0: "Numeral1 = Suc 0"
  by (simp only: numeral_One One_nat_def)

lemma Suc_nat_number_of_add: "Suc (numeral v + n) = numeral (v + One) + n"
  by simp

lemma numerals: "Numeral1 = (1::nat)" "2 = Suc (Suc 0)"
  by (rule numeral_One) (rule numeral_2_eq_2)

lemmas numeral_nat = eval_nat_numeral BitM.simps One_nat_def

text \<open>Comparisons involving \<^term>\<open>Suc\<close>.\<close>

lemma eq_numeral_Suc [simp]: "numeral k = Suc n \<longleftrightarrow> pred_numeral k = n"
  by (simp add: numeral_eq_Suc)

lemma Suc_eq_numeral [simp]: "Suc n = numeral k \<longleftrightarrow> n = pred_numeral k"
  by (simp add: numeral_eq_Suc)

lemma less_numeral_Suc [simp]: "numeral k < Suc n \<longleftrightarrow> pred_numeral k < n"
  by (simp add: numeral_eq_Suc)

lemma less_Suc_numeral [simp]: "Suc n < numeral k \<longleftrightarrow> n < pred_numeral k"
  by (simp add: numeral_eq_Suc)

lemma le_numeral_Suc [simp]: "numeral k \<le> Suc n \<longleftrightarrow> pred_numeral k \<le> n"
  by (simp add: numeral_eq_Suc)

lemma le_Suc_numeral [simp]: "Suc n \<le> numeral k \<longleftrightarrow> n \<le> pred_numeral k"
  by (simp add: numeral_eq_Suc)

lemma diff_Suc_numeral [simp]: "Suc n - numeral k = n - pred_numeral k"
  by (simp add: numeral_eq_Suc)

lemma diff_numeral_Suc [simp]: "numeral k - Suc n = pred_numeral k - n"
  by (simp add: numeral_eq_Suc)

lemma max_Suc_numeral [simp]: "max (Suc n) (numeral k) = Suc (max n (pred_numeral k))"
  by (simp add: numeral_eq_Suc)

lemma max_numeral_Suc [simp]: "max (numeral k) (Suc n) = Suc (max (pred_numeral k) n)"
  by (simp add: numeral_eq_Suc)

lemma min_Suc_numeral [simp]: "min (Suc n) (numeral k) = Suc (min n (pred_numeral k))"
  by (simp add: numeral_eq_Suc)

lemma min_numeral_Suc [simp]: "min (numeral k) (Suc n) = Suc (min (pred_numeral k) n)"
  by (simp add: numeral_eq_Suc)

text \<open>For \<^term>\<open>case_nat\<close> and \<^term>\<open>rec_nat\<close>.\<close>

lemma case_nat_numeral [simp]: "case_nat a f (numeral v) = (let pv = pred_numeral v in f pv)"
  by (simp add: numeral_eq_Suc)

lemma case_nat_add_eq_if [simp]:
  "case_nat a f ((numeral v) + n) = (let pv = pred_numeral v in f (pv + n))"
  by (simp add: numeral_eq_Suc)

lemma rec_nat_numeral [simp]:
  "rec_nat a f (numeral v) = (let pv = pred_numeral v in f pv (rec_nat a f pv))"
  by (simp add: numeral_eq_Suc Let_def)

lemma rec_nat_add_eq_if [simp]:
  "rec_nat a f (numeral v + n) = (let pv = pred_numeral v in f (pv + n) (rec_nat a f (pv + n)))"
  by (simp add: numeral_eq_Suc Let_def)

text \<open>Case analysis on \<^term>\<open>n < 2\<close>.\<close>
lemma less_2_cases: "n < 2 \<Longrightarrow> n = 0 \<or> n = Suc 0"
  by (auto simp add: numeral_2_eq_2)

lemma less_2_cases_iff: "n < 2 \<longleftrightarrow> n = 0 \<or> n = Suc 0"
  by (auto simp add: numeral_2_eq_2)

text \<open>Removal of Small Numerals: 0, 1 and (in additive positions) 2.\<close>
text \<open>bh: Are these rules really a good idea? LCP: well, it already happens for 0 and 1!\<close>

lemma add_2_eq_Suc [simp]: "2 + n = Suc (Suc n)"
  by simp

lemma add_2_eq_Suc' [simp]: "n + 2 = Suc (Suc n)"
  by simp

text \<open>Can be used to eliminate long strings of Sucs, but not by default.\<close>
lemma Suc3_eq_add_3: "Suc (Suc (Suc n)) = 3 + n"
  by simp

lemmas nat_1_add_1 = one_add_one [where 'a=nat] (* legacy *)

context semiring_numeral
begin

lemma numeral_add_unfold_funpow:
  \<open>numeral k + a = ((+) 1 ^^ numeral k) a\<close>
proof (rule sym, induction k arbitrary: a)
  case One
  then show ?case
    by (simp add: numeral_One Num.numeral_One)
next
  case (Bit0 k)
  then show ?case
    by (simp add: numeral_Bit0 Num.numeral_Bit0 ac_simps funpow_add)
next
  case (Bit1 k)
  then show ?case
    by (simp add: numeral_Bit1 Num.numeral_Bit1 ac_simps funpow_add)
qed

end

context semiring_1
begin

lemma numeral_unfold_funpow:
  \<open>numeral k = ((+) 1 ^^ numeral k) 0\<close>
  using numeral_add_unfold_funpow [of k 0] by simp

end

context
  includes lifting_syntax
begin

lemma transfer_rule_numeral:
  \<open>((=) ===> R) numeral numeral\<close>
    if [transfer_rule]: \<open>R 0 0\<close> \<open>R 1 1\<close>
      \<open>(R ===> R ===> R) (+) (+)\<close>
    for R :: \<open>'a::{semiring_numeral,monoid_add} \<Rightarrow> 'b::{semiring_numeral,monoid_add} \<Rightarrow> bool\<close>
proof -
  have "((=) ===> R) (\<lambda>k. ((+) 1 ^^ numeral k) 0) (\<lambda>k. ((+) 1 ^^ numeral k) 0)"
    by transfer_prover
  moreover have \<open>numeral = (\<lambda>k. ((+) (1::'a) ^^ numeral k) 0)\<close>
    using numeral_add_unfold_funpow [where ?'a = 'a, of _ 0]
    by (simp add: fun_eq_iff)
  moreover have \<open>numeral = (\<lambda>k. ((+) (1::'b) ^^ numeral k) 0)\<close>
    using numeral_add_unfold_funpow [where ?'a = 'b, of _ 0]
    by (simp add: fun_eq_iff)
  ultimately show ?thesis
    by simp
qed

end


subsection \<open>Particular lemmas concerning \<^term>\<open>2\<close>\<close>

context linordered_field
begin

subclass field_char_0 ..

lemma half_gt_zero_iff: "0 < a / 2 \<longleftrightarrow> 0 < a"
  by (auto simp add: field_simps)

lemma half_gt_zero [simp]: "0 < a \<Longrightarrow> 0 < a / 2"
  by (simp add: half_gt_zero_iff)

end


subsection \<open>Numeral equations as default simplification rules\<close>

declare (in numeral) numeral_One [simp]
declare (in numeral) numeral_plus_numeral [simp]
declare (in numeral) add_numeral_special [simp]
declare (in neg_numeral) add_neg_numeral_simps [simp]
declare (in neg_numeral) add_neg_numeral_special [simp]
declare (in neg_numeral) diff_numeral_simps [simp]
declare (in neg_numeral) diff_numeral_special [simp]
declare (in semiring_numeral) numeral_times_numeral [simp]
declare (in ring_1) mult_neg_numeral_simps [simp]


subsubsection \<open>Special Simplification for Constants\<close>

text \<open>These distributive laws move literals inside sums and differences.\<close>

lemmas distrib_right_numeral [simp] = distrib_right [of _ _ "numeral v"] for v
lemmas distrib_left_numeral [simp] = distrib_left [of "numeral v"] for v
lemmas left_diff_distrib_numeral [simp] = left_diff_distrib [of _ _ "numeral v"] for v
lemmas right_diff_distrib_numeral [simp] = right_diff_distrib [of "numeral v"] for v

text \<open>These are actually for fields, like real\<close>

lemmas zero_less_divide_iff_numeral [simp, no_atp] = zero_less_divide_iff [of "numeral w"] for w
lemmas divide_less_0_iff_numeral [simp, no_atp] = divide_less_0_iff [of "numeral w"] for w
lemmas zero_le_divide_iff_numeral [simp, no_atp] = zero_le_divide_iff [of "numeral w"] for w
lemmas divide_le_0_iff_numeral [simp, no_atp] = divide_le_0_iff [of "numeral w"] for w

text \<open>Replaces \<open>inverse #nn\<close> by \<open>1/#nn\<close>.  It looks
  strange, but then other simprocs simplify the quotient.\<close>

lemmas inverse_eq_divide_numeral [simp] =
  inverse_eq_divide [of "numeral w"] for w

lemmas inverse_eq_divide_neg_numeral [simp] =
  inverse_eq_divide [of "- numeral w"] for w

text \<open>These laws simplify inequalities, moving unary minus from a term
  into the literal.\<close>

lemmas equation_minus_iff_numeral [no_atp] =
  equation_minus_iff [of "numeral v"] for v

lemmas minus_equation_iff_numeral [no_atp] =
  minus_equation_iff [of _ "numeral v"] for v

lemmas le_minus_iff_numeral [no_atp] =
  le_minus_iff [of "numeral v"] for v

lemmas minus_le_iff_numeral [no_atp] =
  minus_le_iff [of _ "numeral v"] for v

lemmas less_minus_iff_numeral [no_atp] =
  less_minus_iff [of "numeral v"] for v

lemmas minus_less_iff_numeral [no_atp] =
  minus_less_iff [of _ "numeral v"] for v

(* FIXME maybe simproc *)

text \<open>Cancellation of constant factors in comparisons (\<open><\<close> and \<open>\<le>\<close>)\<close>

lemmas mult_less_cancel_left_numeral [simp, no_atp] = mult_less_cancel_left [of "numeral v"] for v
lemmas mult_less_cancel_right_numeral [simp, no_atp] = mult_less_cancel_right [of _ "numeral v"] for v
lemmas mult_le_cancel_left_numeral [simp, no_atp] = mult_le_cancel_left [of "numeral v"] for v
lemmas mult_le_cancel_right_numeral [simp, no_atp] = mult_le_cancel_right [of _ "numeral v"] for v

text \<open>Multiplying out constant divisors in comparisons (\<open><\<close>, \<open>\<le>\<close> and \<open>=\<close>)\<close>

named_theorems divide_const_simps "simplification rules to simplify comparisons involving constant divisors"

lemmas le_divide_eq_numeral1 [simp,divide_const_simps] =
  pos_le_divide_eq [of "numeral w", OF zero_less_numeral]
  neg_le_divide_eq [of "- numeral w", OF neg_numeral_less_zero] for w

lemmas divide_le_eq_numeral1 [simp,divide_const_simps] =
  pos_divide_le_eq [of "numeral w", OF zero_less_numeral]
  neg_divide_le_eq [of "- numeral w", OF neg_numeral_less_zero] for w

lemmas less_divide_eq_numeral1 [simp,divide_const_simps] =
  pos_less_divide_eq [of "numeral w", OF zero_less_numeral]
  neg_less_divide_eq [of "- numeral w", OF neg_numeral_less_zero] for w

lemmas divide_less_eq_numeral1 [simp,divide_const_simps] =
  pos_divide_less_eq [of "numeral w", OF zero_less_numeral]
  neg_divide_less_eq [of "- numeral w", OF neg_numeral_less_zero] for w

lemmas eq_divide_eq_numeral1 [simp,divide_const_simps] =
  eq_divide_eq [of _ _ "numeral w"]
  eq_divide_eq [of _ _ "- numeral w"] for w

lemmas divide_eq_eq_numeral1 [simp,divide_const_simps] =
  divide_eq_eq [of _ "numeral w"]
  divide_eq_eq [of _ "- numeral w"] for w


subsubsection \<open>Optional Simplification Rules Involving Constants\<close>

text \<open>Simplify quotients that are compared with a literal constant.\<close>

lemmas le_divide_eq_numeral [divide_const_simps] =
  le_divide_eq [of "numeral w"]
  le_divide_eq [of "- numeral w"] for w

lemmas divide_le_eq_numeral [divide_const_simps] =
  divide_le_eq [of _ _ "numeral w"]
  divide_le_eq [of _ _ "- numeral w"] for w

lemmas less_divide_eq_numeral [divide_const_simps] =
  less_divide_eq [of "numeral w"]
  less_divide_eq [of "- numeral w"] for w

lemmas divide_less_eq_numeral [divide_const_simps] =
  divide_less_eq [of _ _ "numeral w"]
  divide_less_eq [of _ _ "- numeral w"] for w

lemmas eq_divide_eq_numeral [divide_const_simps] =
  eq_divide_eq [of "numeral w"]
  eq_divide_eq [of "- numeral w"] for w

lemmas divide_eq_eq_numeral [divide_const_simps] =
  divide_eq_eq [of _ _ "numeral w"]
  divide_eq_eq [of _ _ "- numeral w"] for w

text \<open>Not good as automatic simprules because they cause case splits.\<close>

lemmas [divide_const_simps] =
  le_divide_eq_1 divide_le_eq_1 less_divide_eq_1 divide_less_eq_1


subsection \<open>Setting up simprocs\<close>

lemma mult_numeral_1: "Numeral1 * a = a"
  for a :: "'a::semiring_numeral"
  by simp

lemma mult_numeral_1_right: "a * Numeral1 = a"
  for a :: "'a::semiring_numeral"
  by simp

lemma divide_numeral_1: "a / Numeral1 = a"
  for a :: "'a::field"
  by simp

lemma inverse_numeral_1: "inverse Numeral1 = (Numeral1::'a::division_ring)"
  by simp

text \<open>
  Theorem lists for the cancellation simprocs. The use of a binary
  numeral for 1 reduces the number of special cases.
\<close>

lemma mult_1s_semiring_numeral:
  "Numeral1 * a = a"
  "a * Numeral1 = a"
  for a :: "'a::semiring_numeral"
  by simp_all

lemma mult_1s_ring_1:
  "- Numeral1 * b = - b"
  "b * - Numeral1 = - b"
  for b :: "'a::ring_1"
  by simp_all

lemmas mult_1s = mult_1s_semiring_numeral mult_1s_ring_1

setup \<open>
  Reorient_Proc.add
    (fn Const (\<^const_name>\<open>numeral\<close>, _) $ _ => true
      | Const (\<^const_name>\<open>uminus\<close>, _) $ (Const (\<^const_name>\<open>numeral\<close>, _) $ _) => true
      | _ => false)
\<close>

simproc_setup reorient_numeral ("numeral w = x" | "- numeral w = y") =
  \<open>K Reorient_Proc.proc\<close>


subsubsection \<open>Simplification of arithmetic operations on integer constants\<close>

lemmas arith_special = (* already declared simp above *)
  add_numeral_special add_neg_numeral_special
  diff_numeral_special

lemmas arith_extra_simps = (* rules already in simpset *)
  numeral_plus_numeral add_neg_numeral_simps add_0_left add_0_right
  minus_zero
  diff_numeral_simps diff_0 diff_0_right
  numeral_times_numeral mult_neg_numeral_simps
  mult_zero_left mult_zero_right
  abs_numeral abs_neg_numeral

text \<open>
  For making a minimal simpset, one must include these default simprules.
  Also include \<open>simp_thms\<close>.
\<close>

lemmas arith_simps =
  add_num_simps mult_num_simps sub_num_simps
  BitM.simps dbl_simps dbl_inc_simps dbl_dec_simps
  abs_zero abs_one arith_extra_simps

lemmas more_arith_simps =
  neg_le_iff_le
  minus_zero left_minus right_minus
  mult_1_left mult_1_right
  mult_minus_left mult_minus_right
  minus_add_distrib minus_minus mult.assoc

lemmas of_nat_simps =
  of_nat_0 of_nat_1 of_nat_Suc of_nat_add of_nat_mult

text \<open>Simplification of relational operations.\<close>

lemmas eq_numeral_extra =
  zero_neq_one one_neq_zero

lemmas rel_simps =
  le_num_simps less_num_simps eq_num_simps
  le_numeral_simps le_neg_numeral_simps le_minus_one_simps le_numeral_extra
  less_numeral_simps less_neg_numeral_simps less_minus_one_simps less_numeral_extra
  eq_numeral_simps eq_neg_numeral_simps eq_numeral_extra

lemma Let_numeral [simp]: "Let (numeral v) f = f (numeral v)"
  \<comment> \<open>Unfold all \<open>let\<close>s involving constants\<close>
  unfolding Let_def ..

lemma Let_neg_numeral [simp]: "Let (- numeral v) f = f (- numeral v)"
  \<comment> \<open>Unfold all \<open>let\<close>s involving constants\<close>
  unfolding Let_def ..

declaration \<open>
let
  fun number_of ctxt T n =
    if not (Sign.of_sort (Proof_Context.theory_of ctxt) (T, \<^sort>\<open>numeral\<close>))
    then raise CTERM ("number_of", [])
    else Numeral.mk_cnumber (Thm.ctyp_of ctxt T) n;
in
  K (
    Lin_Arith.set_number_of number_of
    #> Lin_Arith.add_simps
      @{thms arith_simps more_arith_simps rel_simps pred_numeral_simps
        arith_special numeral_One of_nat_simps uminus_numeral_One
        Suc_numeral Let_numeral Let_neg_numeral Let_0 Let_1
        le_Suc_numeral le_numeral_Suc less_Suc_numeral less_numeral_Suc
        Suc_eq_numeral eq_numeral_Suc mult_Suc mult_Suc_right of_nat_numeral})
end
\<close>


subsubsection \<open>Simplification of arithmetic when nested to the right\<close>

lemma add_numeral_left [simp]: "numeral v + (numeral w + z) = (numeral(v + w) + z)"
  by (simp_all add: add.assoc [symmetric])

lemma add_neg_numeral_left [simp]:
  "numeral v + (- numeral w + y) = (sub v w + y)"
  "- numeral v + (numeral w + y) = (sub w v + y)"
  "- numeral v + (- numeral w + y) = (- numeral(v + w) + y)"
  by (simp_all add: add.assoc [symmetric])

lemma mult_numeral_left_semiring_numeral:
  "numeral v * (numeral w * z) = (numeral(v * w) * z :: 'a::semiring_numeral)"
  by (simp add: mult.assoc [symmetric])

lemma mult_numeral_left_ring_1:
  "- numeral v * (numeral w * y) = (- numeral(v * w) * y :: 'a::ring_1)"
  "numeral v * (- numeral w * y) = (- numeral(v * w) * y :: 'a::ring_1)"
  "- numeral v * (- numeral w * y) = (numeral(v * w) * y :: 'a::ring_1)"
  by (simp_all add: mult.assoc [symmetric])

lemmas mult_numeral_left [simp] =
  mult_numeral_left_semiring_numeral
  mult_numeral_left_ring_1

hide_const (open) One Bit0 Bit1 BitM inc pow sqr sub dbl dbl_inc dbl_dec


subsection \<open>Code module namespace\<close>

code_identifier
  code_module Num \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

subsection \<open>Printing of evaluated natural numbers as numerals\<close>

lemma [code_post]:
  "Suc 0 = 1"
  "Suc 1 = 2"
  "Suc (numeral n) = numeral (Num.inc n)"
  by (simp_all add: numeral_inc)

lemmas [code_post] = Num.inc.simps


subsection \<open>More on auxiliary conversion\<close>

context semiring_1
begin

lemma numeral_num_of_nat_unfold:
  \<open>numeral (num_of_nat n) = (if n = 0 then 1 else of_nat n)\<close>
  by (induction n) (simp_all add: numeral_inc ac_simps)

lemma num_of_nat_numeral_eq [simp]:
  \<open>num_of_nat (numeral q) = q\<close>
proof (induction q)
  case One
  then show ?case
    by simp
next
  case (Bit0 q)
  then have "num_of_nat (numeral (num.Bit0 q)) = num_of_nat (numeral q + numeral q)"
    by (simp only: Num.numeral_Bit0 Num.numeral_add)
  also have "\<dots> = num.Bit0 (num_of_nat (numeral q))"
    by (rule num_of_nat_double) simp
  finally show ?case
    using Bit0.IH by simp
next
  case (Bit1 q)
  then have "num_of_nat (numeral (num.Bit1 q)) = num_of_nat (numeral q + numeral q + 1)"
    by (simp only: Num.numeral_Bit1 Num.numeral_add)
  also have "\<dots> = num_of_nat (numeral q + numeral q) + num_of_nat 1"
    by (rule num_of_nat_plus_distrib) auto
  also have "\<dots> = num.Bit0 (num_of_nat (numeral q)) + num_of_nat 1"
    by (subst num_of_nat_double) auto
  finally show ?case
    using Bit1.IH by simp
qed

end

end
