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

primrec inc :: \<open>num \<Rightarrow> num\<close>
  where
    \<open>inc One = Bit0 One\<close>
  | \<open>inc (Bit0 x) = Bit1 x\<close>
  | \<open>inc (Bit1 x) = Bit0 (inc x)\<close>

text \<open>Converting between type \<^typ>\<open>num\<close> and type \<^typ>\<open>nat\<close>\<close>

primrec nat_of_num :: \<open>num \<Rightarrow> nat\<close>
  where
    \<open>nat_of_num One = Suc 0\<close>
  | \<open>nat_of_num (Bit0 x) = nat_of_num x + nat_of_num x\<close>
  | \<open>nat_of_num (Bit1 x) = Suc (nat_of_num x + nat_of_num x)\<close>

primrec num_of_nat :: \<open>nat \<Rightarrow> num\<close>
  where
    \<open>num_of_nat 0 = One\<close>
  | \<open>num_of_nat (Suc n) = (if 0 < n then inc (num_of_nat n) else One)\<close>

lemma nat_of_num_pos: \<open>0 < nat_of_num x\<close>
  by (induct x) simp_all

lemma nat_of_num_neq_0: \<open> nat_of_num x \<noteq> 0\<close>
  by (induct x) simp_all

lemma nat_of_num_inc: \<open>nat_of_num (inc x) = Suc (nat_of_num x)\<close>
  by (induct x) simp_all

lemma num_of_nat_double: \<open>0 < n \<Longrightarrow> num_of_nat (n + n) = Bit0 (num_of_nat n)\<close>
  by (induct n) simp_all

text \<open>Type \<^typ>\<open>num\<close> is isomorphic to the strictly positive natural numbers.\<close>

lemma nat_of_num_inverse: \<open>num_of_nat (nat_of_num x) = x\<close>
  by (induct x) (simp_all add: num_of_nat_double nat_of_num_pos)

lemma num_of_nat_inverse: \<open>0 < n \<Longrightarrow> nat_of_num (num_of_nat n) = n\<close>
  by (induct n) (simp_all add: nat_of_num_inc)

lemma num_eq_iff: \<open>x = y \<longleftrightarrow> nat_of_num x = nat_of_num y\<close>
  apply safe
  apply (drule arg_cong [where f=num_of_nat])
  apply (simp add: nat_of_num_inverse)
  done

lemma num_induct [case_names One inc]:
  fixes P :: \<open>num \<Rightarrow> bool\<close>
  assumes One: \<open>P One\<close>
    and inc: \<open>\<And>x. P x \<Longrightarrow> P (inc x)\<close>
  shows \<open>P x\<close>
proof -
  obtain n where n: \<open>Suc n = nat_of_num x\<close>
    by (cases \<open>nat_of_num x\<close>) (simp_all add: nat_of_num_neq_0)
  have \<open>P (num_of_nat (Suc n))\<close>
  proof (induct n)
    case 0
    from One show ?case by simp
  next
    case (Suc n)
    then have \<open>P (inc (num_of_nat (Suc n)))\<close> by (rule inc)
    then show \<open>P (num_of_nat (Suc (Suc n)))\<close> by simp
  qed
  with n show \<open>P x\<close>
    by (simp add: nat_of_num_inverse)
qed

text \<open>
  From now on, there are two possible models for \<^typ>\<open>num\<close>: as positive
  naturals (rule \<open>num_induct\<close>) and as digit representation (rules
  \<open>num.induct\<close>, \<open>num.cases\<close>).
\<close>


subsection \<open>Numeral operations\<close>

instantiation num :: \<open>{plus,times,linorder}\<close>
begin

definition \<open>m + n = num_of_nat (nat_of_num m + nat_of_num n)\<close>

definition \<open>m * n = num_of_nat (nat_of_num m * nat_of_num n)\<close>

definition \<open>m \<le> n \<longleftrightarrow> nat_of_num m \<le> nat_of_num n\<close>

definition \<open>m < n \<longleftrightarrow> nat_of_num m < nat_of_num n\<close>

instance
  by standard (auto simp add: less_num_def less_eq_num_def num_eq_iff)

end

lemma nat_of_num_add: \<open>nat_of_num (x + y) = nat_of_num x + nat_of_num y\<close>
  unfolding plus_num_def
  by (intro num_of_nat_inverse add_pos_pos nat_of_num_pos)

lemma nat_of_num_mult: \<open>nat_of_num (x * y) = nat_of_num x * nat_of_num y\<close>
  unfolding times_num_def
  by (intro num_of_nat_inverse mult_pos_pos nat_of_num_pos)

lemma add_num_simps [simp, code]:
  \<open>One + One = Bit0 One\<close>
  \<open>One + Bit0 n = Bit1 n\<close>
  \<open>One + Bit1 n = Bit0 (n + One)\<close>
  \<open>Bit0 m + One = Bit1 m\<close>
  \<open>Bit0 m + Bit0 n = Bit0 (m + n)\<close>
  \<open>Bit0 m + Bit1 n = Bit1 (m + n)\<close>
  \<open>Bit1 m + One = Bit0 (m + One)\<close>
  \<open>Bit1 m + Bit0 n = Bit1 (m + n)\<close>
  \<open>Bit1 m + Bit1 n = Bit0 (m + n + One)\<close>
  by (simp_all add: num_eq_iff nat_of_num_add)

lemma mult_num_simps [simp, code]:
  \<open>m * One = m\<close>
  \<open>One * n = n\<close>
  \<open>Bit0 m * Bit0 n = Bit0 (Bit0 (m * n))\<close>
  \<open>Bit0 m * Bit1 n = Bit0 (m * Bit1 n)\<close>
  \<open>Bit1 m * Bit0 n = Bit0 (Bit1 m * n)\<close>
  \<open>Bit1 m * Bit1 n = Bit1 (m + n + Bit0 (m * n))\<close>
  by (simp_all add: num_eq_iff nat_of_num_add nat_of_num_mult distrib_right distrib_left)

lemma eq_num_simps:
  \<open>One = One \<longleftrightarrow> True\<close>
  \<open>One = Bit0 n \<longleftrightarrow> False\<close>
  \<open>One = Bit1 n \<longleftrightarrow> False\<close>
  \<open>Bit0 m = One \<longleftrightarrow> False\<close>
  \<open>Bit1 m = One \<longleftrightarrow> False\<close>
  \<open>Bit0 m = Bit0 n \<longleftrightarrow> m = n\<close>
  \<open>Bit0 m = Bit1 n \<longleftrightarrow> False\<close>
  \<open>Bit1 m = Bit0 n \<longleftrightarrow> False\<close>
  \<open>Bit1 m = Bit1 n \<longleftrightarrow> m = n\<close>
  by simp_all

lemma le_num_simps [simp, code]:
  \<open>One \<le> n \<longleftrightarrow> True\<close>
  \<open>Bit0 m \<le> One \<longleftrightarrow> False\<close>
  \<open>Bit1 m \<le> One \<longleftrightarrow> False\<close>
  \<open>Bit0 m \<le> Bit0 n \<longleftrightarrow> m \<le> n\<close>
  \<open>Bit0 m \<le> Bit1 n \<longleftrightarrow> m \<le> n\<close>
  \<open>Bit1 m \<le> Bit1 n \<longleftrightarrow> m \<le> n\<close>
  \<open>Bit1 m \<le> Bit0 n \<longleftrightarrow> m < n\<close>
  using nat_of_num_pos [of n] nat_of_num_pos [of m]
  by (auto simp add: less_eq_num_def less_num_def)

lemma less_num_simps [simp, code]:
  \<open>m < One \<longleftrightarrow> False\<close>
  \<open>One < Bit0 n \<longleftrightarrow> True\<close>
  \<open>One < Bit1 n \<longleftrightarrow> True\<close>
  \<open>Bit0 m < Bit0 n \<longleftrightarrow> m < n\<close>
  \<open>Bit0 m < Bit1 n \<longleftrightarrow> m \<le> n\<close>
  \<open>Bit1 m < Bit1 n \<longleftrightarrow> m < n\<close>
  \<open>Bit1 m < Bit0 n \<longleftrightarrow> m < n\<close>
  using nat_of_num_pos [of n] nat_of_num_pos [of m]
  by (auto simp add: less_eq_num_def less_num_def)

lemma le_num_One_iff: \<open>x \<le> One \<longleftrightarrow> x = One\<close>
  by (simp add: antisym_conv)

text \<open>Rules using \<open>One\<close> and \<open>inc\<close> as constructors.\<close>

lemma add_One: \<open>x + One = inc x\<close>
  by (simp add: num_eq_iff nat_of_num_add nat_of_num_inc)

lemma add_One_commute: \<open>One + n = n + One\<close>
  by (induct n) simp_all

lemma add_inc: \<open>x + inc y = inc (x + y)\<close>
  by (simp add: num_eq_iff nat_of_num_add nat_of_num_inc)

lemma mult_inc: \<open>x * inc y = x * y + x\<close>
  by (simp add: num_eq_iff nat_of_num_mult nat_of_num_add nat_of_num_inc)

text \<open>The \<^const>\<open>num_of_nat\<close> conversion.\<close>

lemma num_of_nat_One: \<open>n \<le> 1 \<Longrightarrow> num_of_nat n = One\<close>
  by (cases n) simp_all

lemma num_of_nat_plus_distrib:
  \<open>0 < m \<Longrightarrow> 0 < n \<Longrightarrow> num_of_nat (m + n) = num_of_nat m + num_of_nat n\<close>
  by (induct n) (auto simp add: add_One add_One_commute add_inc)

text \<open>A double-and-decrement function.\<close>

primrec BitM :: \<open>num \<Rightarrow> num\<close>
  where
    \<open>BitM One = One\<close>
  | \<open>BitM (Bit0 n) = Bit1 (BitM n)\<close>
  | \<open>BitM (Bit1 n) = Bit1 (Bit0 n)\<close>

lemma BitM_plus_one: \<open>BitM n + One = Bit0 n\<close>
  by (induct n) simp_all

lemma one_plus_BitM: \<open>One + BitM n = Bit0 n\<close>
  unfolding add_One_commute BitM_plus_one ..

lemma BitM_inc_eq:
  \<open>BitM (inc n) = Bit1 n\<close>
  by (induction n) simp_all

lemma inc_BitM_eq:
  \<open>inc (BitM n) = Bit0 n\<close>
  by (simp add: BitM_plus_one[symmetric] add_One)

text \<open>Squaring and exponentiation.\<close>

primrec sqr :: \<open>num \<Rightarrow> num\<close>
  where
    \<open>sqr One = One\<close>
  | \<open>sqr (Bit0 n) = Bit0 (Bit0 (sqr n))\<close>
  | \<open>sqr (Bit1 n) = Bit1 (Bit0 (sqr n + n))\<close>

primrec pow :: \<open>num \<Rightarrow> num \<Rightarrow> num\<close>
  where
    \<open>pow x One = x\<close>
  | \<open>pow x (Bit0 y) = sqr (pow x y)\<close>
  | \<open>pow x (Bit1 y) = sqr (pow x y) * x\<close>

lemma nat_of_num_sqr: \<open>nat_of_num (sqr x) = nat_of_num x * nat_of_num x\<close>
  by (induct x) (simp_all add: algebra_simps nat_of_num_add)

lemma sqr_conv_mult: \<open>sqr x = x * x\<close>
  by (simp add: num_eq_iff nat_of_num_sqr nat_of_num_mult)

lemma num_double [simp]:
  \<open>Bit0 num.One * n = Bit0 n\<close>
  by (simp add: num_eq_iff nat_of_num_mult)


subsection \<open>Binary numerals\<close>

text \<open>
  We embed binary representations into a generic algebraic
  structure using \<open>numeral\<close>.
\<close>

class numeral = one + semigroup_add
begin

primrec numeral :: \<open>num \<Rightarrow> 'a\<close>
  where
    numeral_One: \<open>numeral One = 1\<close>
  | numeral_Bit0: \<open>numeral (Bit0 n) = numeral n + numeral n\<close>
  | numeral_Bit1: \<open>numeral (Bit1 n) = numeral n + numeral n + 1\<close>

lemma numeral_code [code]:
  \<open>numeral One = 1\<close>
  \<open>numeral (Bit0 n) = (let m = numeral n in m + m)\<close>
  \<open>numeral (Bit1 n) = (let m = numeral n in m + m + 1)\<close>
  by (simp_all add: Let_def)

lemma one_plus_numeral_commute: \<open>1 + numeral x = numeral x + 1\<close>
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

lemma numeral_inc: \<open>numeral (inc x) = numeral x + 1\<close>
proof (induct x)
  case One
  then show ?case by simp
next
  case Bit0
  then show ?case by simp
next
  case (Bit1 x)
  have \<open>numeral x + (1 + numeral x) + 1 = numeral x + (numeral x + 1) + 1\<close>
    by (simp only: one_plus_numeral_commute)
  with Bit1 show ?case
    by (simp add: add.assoc)
qed

declare numeral.simps [simp del]

abbreviation \<open>Numeral1 \<equiv> numeral One\<close>

declare numeral_One [code_post]

end

text \<open>Numeral syntax.\<close>

syntax
  "_Numeral" :: \<open>num_const \<Rightarrow> 'a\<close>  (\<open>(\<open>open_block notation=\<open>literal number\<close>\<close>_)\<close>)

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

lemma numeral_add: \<open>numeral (m + n) = numeral m + numeral n\<close>
  by (induct n rule: num_induct)
    (simp_all only: numeral_One add_One add_inc numeral_inc add.assoc)

lemma numeral_plus_numeral: \<open>numeral m + numeral n = numeral (m + n)\<close>
  by (rule numeral_add [symmetric])

lemma numeral_plus_one: \<open>numeral n + 1 = numeral (n + One)\<close>
  using numeral_add [of n One] by (simp add: numeral_One)

lemma one_plus_numeral: \<open>1 + numeral n = numeral (One + n)\<close>
  using numeral_add [of One n] by (simp add: numeral_One)

lemma one_add_one: \<open>1 + 1 = 2\<close>
  using numeral_add [of One One] by (simp add: numeral_One)

lemmas add_numeral_special =
  numeral_plus_one one_plus_numeral one_add_one

end


subsubsection \<open>Structures with negation: class \<open>neg_numeral\<close>\<close>

class neg_numeral = numeral + group_add
begin

lemma uminus_numeral_One: \<open>- Numeral1 = - 1\<close>
  by (simp add: numeral_One)

text \<open>Numerals form an abelian subgroup.\<close>

inductive is_num :: \<open>'a \<Rightarrow> bool\<close>
  where
    \<open>is_num 1\<close>
  | \<open>is_num x \<Longrightarrow> is_num (- x)\<close>
  | \<open>is_num x \<Longrightarrow> is_num y \<Longrightarrow> is_num (x + y)\<close>

lemma is_num_numeral: \<open>is_num (numeral k)\<close>
  by (induct k) (simp_all add: numeral.simps is_num.intros)

lemma is_num_add_commute: \<open>is_num x \<Longrightarrow> is_num y \<Longrightarrow> x + y = y + x\<close>
proof(induction x rule: is_num.induct)
  case 1
  then show ?case
  proof (induction y rule: is_num.induct)
    case 1
    then show ?case by simp
  next
    case (2 y)
    then have \<open>y + (1 + - y) + y = y + (- y + 1) + y\<close>
      by (simp add: add.assoc)
    then have \<open>y + (1 + - y) = y + (- y + 1)\<close>
      by simp
    then show ?case
      by (rule add_left_imp_eq[of y])
  next
    case (3 x y)
    then have \<open>1 + (x + y) = x + 1 + y\<close>
      by (simp add: add.assoc [symmetric])
    then show ?case using 3
      by (simp add: add.assoc)
  qed
next
  case (2 x)
  then have \<open>x + (- x + y) + x = x + (y + - x) + x\<close>
    by (simp add: add.assoc)
  then have \<open>x + (- x + y) = x + (y + - x)\<close>
    by simp
  then show ?case
    by (rule add_left_imp_eq[of x])
next
  case (3 x z)
  moreover have \<open>x + (y + z) = (x + y) + z\<close>
    by (simp add: add.assoc[symmetric])
  ultimately show ?case 
    by (simp add: add.assoc)
qed

lemma is_num_add_left_commute: \<open>is_num x \<Longrightarrow> is_num y \<Longrightarrow> x + (y + z) = y + (x + z)\<close>
  by (simp only: add.assoc [symmetric] is_num_add_commute)

lemmas is_num_normalize =
  add.assoc is_num_add_commute is_num_add_left_commute
  is_num.intros is_num_numeral
  minus_add

definition dbl :: \<open>'a \<Rightarrow> 'a\<close>
  where \<open>dbl x = x + x\<close>

definition dbl_inc :: \<open>'a \<Rightarrow> 'a\<close>
  where \<open>dbl_inc x = x + x + 1\<close>

definition dbl_dec :: \<open>'a \<Rightarrow> 'a\<close>
  where \<open>dbl_dec x = x + x - 1\<close>

definition sub :: \<open>num \<Rightarrow> num \<Rightarrow> 'a\<close>
  where \<open>sub k l = numeral k - numeral l\<close>

lemma numeral_BitM: \<open>numeral (BitM n) = numeral (Bit0 n) - 1\<close>
  by (simp only: BitM_plus_one [symmetric] numeral_add numeral_One eq_diff_eq)

lemma sub_inc_One_eq:
  \<open>sub (inc n) num.One = numeral n\<close>
  by (simp_all add: sub_def diff_eq_eq numeral_inc numeral.numeral_One)

lemma dbl_simps [simp]:
  \<open>dbl (- numeral k) = - dbl (numeral k)\<close>
  \<open>dbl 0 = 0\<close>
  \<open>dbl 1 = 2\<close>
  \<open>dbl (- 1) = - 2\<close>
  \<open>dbl (numeral k) = numeral (Bit0 k)\<close>
  by (simp_all add: dbl_def numeral.simps minus_add)

lemma dbl_inc_simps [simp]:
  \<open>dbl_inc (- numeral k) = - dbl_dec (numeral k)\<close>
  \<open>dbl_inc 0 = 1\<close>
  \<open>dbl_inc 1 = 3\<close>
  \<open>dbl_inc (- 1) = - 1\<close>
  \<open>dbl_inc (numeral k) = numeral (Bit1 k)\<close>
  by (simp_all add: dbl_inc_def dbl_dec_def numeral.simps numeral_BitM is_num_normalize algebra_simps
      del: add_uminus_conv_diff)

lemma dbl_dec_simps [simp]:
  \<open>dbl_dec (- numeral k) = - dbl_inc (numeral k)\<close>
  \<open>dbl_dec 0 = - 1\<close>
  \<open>dbl_dec 1 = 1\<close>
  \<open>dbl_dec (- 1) = - 3\<close>
  \<open>dbl_dec (numeral k) = numeral (BitM k)\<close>
  by (simp_all add: dbl_dec_def dbl_inc_def numeral.simps numeral_BitM is_num_normalize)

lemma sub_num_simps [simp]:
  \<open>sub One One = 0\<close>
  \<open>sub One (Bit0 l) = - numeral (BitM l)\<close>
  \<open>sub One (Bit1 l) = - numeral (Bit0 l)\<close>
  \<open>sub (Bit0 k) One = numeral (BitM k)\<close>
  \<open>sub (Bit1 k) One = numeral (Bit0 k)\<close>
  \<open>sub (Bit0 k) (Bit0 l) = dbl (sub k l)\<close>
  \<open>sub (Bit0 k) (Bit1 l) = dbl_dec (sub k l)\<close>
  \<open>sub (Bit1 k) (Bit0 l) = dbl_inc (sub k l)\<close>
  \<open>sub (Bit1 k) (Bit1 l) = dbl (sub k l)\<close>
  by (simp_all add: dbl_def dbl_dec_def dbl_inc_def sub_def numeral.simps
    numeral_BitM is_num_normalize del: add_uminus_conv_diff add: diff_conv_add_uminus)

lemma add_neg_numeral_simps:
  \<open>numeral m + - numeral n = sub m n\<close>
  \<open>- numeral m + numeral n = sub n m\<close>
  \<open>- numeral m + - numeral n = - (numeral m + numeral n)\<close>
  by (simp_all add: sub_def numeral_add numeral.simps is_num_normalize
      del: add_uminus_conv_diff add: diff_conv_add_uminus)

lemma add_neg_numeral_special:
  \<open>1 + - numeral m = sub One m\<close>
  \<open>- numeral m + 1 = sub One m\<close>
  \<open>numeral m + - 1 = sub m One\<close>
  \<open>- 1 + numeral n = sub n One\<close>
  \<open>- 1 + - numeral n = - numeral (inc n)\<close>
  \<open>- numeral m + - 1 = - numeral (inc m)\<close>
  \<open>1 + - 1 = 0\<close>
  \<open>- 1 + 1 = 0\<close>
  \<open>- 1 + - 1 = - 2\<close>
  by (simp_all add: sub_def numeral_add numeral.simps is_num_normalize right_minus numeral_inc
      del: add_uminus_conv_diff add: diff_conv_add_uminus)

lemma diff_numeral_simps:
  \<open>numeral m - numeral n = sub m n\<close>
  \<open>numeral m - - numeral n = numeral (m + n)\<close>
  \<open>- numeral m - numeral n = - numeral (m + n)\<close>
  \<open>- numeral m - - numeral n = sub n m\<close>
  by (simp_all add: sub_def numeral_add numeral.simps is_num_normalize
      del: add_uminus_conv_diff add: diff_conv_add_uminus)

lemma diff_numeral_special:
  \<open>1 - numeral n = sub One n\<close>
  \<open>numeral m - 1 = sub m One\<close>
  \<open>1 - - numeral n = numeral (One + n)\<close>
  \<open>- numeral m - 1 = - numeral (m + One)\<close>
  \<open>- 1 - numeral n = - numeral (inc n)\<close>
  \<open>numeral m - - 1 = numeral (inc m)\<close>
  \<open>- 1 - - numeral n = sub n One\<close>
  \<open>- numeral m - - 1 = sub One m\<close>
  \<open>1 - 1 = 0\<close>
  \<open>- 1 - 1 = - 2\<close>
  \<open>1 - - 1 = 2\<close>
  \<open>- 1 - - 1 = 0\<close>
  by (simp_all add: sub_def numeral_add numeral.simps is_num_normalize numeral_inc
      del: add_uminus_conv_diff add: diff_conv_add_uminus)

end


subsubsection \<open>Structures with multiplication: class \<open>semiring_numeral\<close>\<close>

class semiring_numeral = semiring + monoid_mult
begin

subclass numeral ..

lemma numeral_mult: \<open>numeral (m * n) = numeral m * numeral n\<close>
  by (induct n rule: num_induct)
    (simp_all add: numeral_One mult_inc numeral_inc numeral_add distrib_left)

lemma numeral_times_numeral: \<open>numeral m * numeral n = numeral (m * n)\<close>
  by (rule numeral_mult [symmetric])

lemma mult_2: \<open>2 * z = z + z\<close>
  by (simp add: one_add_one [symmetric] distrib_right)

lemma mult_2_right: \<open>z * 2 = z + z\<close>
  by (simp add: one_add_one [symmetric] distrib_left)

lemma left_add_twice:
  \<open>a + (a + b) = 2 * a + b\<close>
  by (simp add: mult_2 ac_simps)

lemma numeral_Bit0_eq_double:
  \<open>numeral (Bit0 n) = 2 * numeral n\<close>
  by (simp add: mult_2) (simp add: numeral_Bit0)

lemma numeral_Bit1_eq_inc_double:
  \<open>numeral (Bit1 n) = 2 * numeral n + 1\<close>
  by (simp add: mult_2) (simp add: numeral_Bit1)

end


subsubsection \<open>Structures with a zero: class \<open>semiring_1\<close>\<close>

context semiring_1
begin

subclass semiring_numeral ..

lemma of_nat_numeral [simp]: \<open>of_nat (numeral n) = numeral n\<close>
  by (induct n) (simp_all only: numeral.simps numeral_class.numeral.simps of_nat_add of_nat_1)

end

lemma nat_of_num_numeral [code_abbrev]: \<open>nat_of_num = numeral\<close>
proof
  fix n
  have \<open>numeral n = nat_of_num n\<close>
    by (induct n) (simp_all add: numeral.simps)
  then show \<open>nat_of_num n = numeral n\<close>
    by simp
qed

lemma nat_of_num_code [code]:
  \<open>nat_of_num One = 1\<close>
  \<open>nat_of_num (Bit0 n) = (let m = nat_of_num n in m + m)\<close>
  \<open>nat_of_num (Bit1 n) = (let m = nat_of_num n in Suc (m + m))\<close>
  by (simp_all add: Let_def)


subsubsection \<open>Equality: class \<open>semiring_char_0\<close>\<close>

context semiring_char_0
begin

lemma numeral_eq_iff: \<open>numeral m = numeral n \<longleftrightarrow> m = n\<close>
  by (simp only: of_nat_numeral [symmetric] nat_of_num_numeral [symmetric]
    of_nat_eq_iff num_eq_iff)

lemma numeral_eq_one_iff: \<open>numeral n = 1 \<longleftrightarrow> n = One\<close>
  by (rule numeral_eq_iff [of n One, unfolded numeral_One])

lemma one_eq_numeral_iff: \<open>1 = numeral n \<longleftrightarrow> One = n\<close>
  by (rule numeral_eq_iff [of One n, unfolded numeral_One])

lemma numeral_neq_zero: \<open>numeral n \<noteq> 0\<close>
  by (simp add: of_nat_numeral [symmetric] nat_of_num_numeral [symmetric] nat_of_num_pos)

lemma zero_neq_numeral: \<open>0 \<noteq> numeral n\<close>
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

lemma numeral_le_iff: \<open>numeral m \<le> numeral n \<longleftrightarrow> m \<le> n\<close>
proof -
  have \<open>of_nat (numeral m) \<le> of_nat (numeral n) \<longleftrightarrow> m \<le> n\<close>
    by (simp only: less_eq_num_def nat_of_num_numeral of_nat_le_iff)
  then show ?thesis by simp
qed

lemma one_le_numeral: \<open>1 \<le> numeral n\<close>
  using numeral_le_iff [of One n] by (simp add: numeral_One)

lemma numeral_le_one_iff: \<open>numeral n \<le> 1 \<longleftrightarrow> n \<le> One\<close>
  using numeral_le_iff [of n One] by (simp add: numeral_One)

lemma numeral_less_iff: \<open>numeral m < numeral n \<longleftrightarrow> m < n\<close>
proof -
  have \<open>of_nat (numeral m) < of_nat (numeral n) \<longleftrightarrow> m < n\<close>
    unfolding less_num_def nat_of_num_numeral of_nat_less_iff ..
  then show ?thesis by simp
qed

lemma not_numeral_less_one: \<open>\<not> numeral n < 1\<close>
  using numeral_less_iff [of n One] by (simp add: numeral_One)

lemma one_less_numeral_iff: \<open>1 < numeral n \<longleftrightarrow> One < n\<close>
  using numeral_less_iff [of One n] by (simp add: numeral_One)

lemma zero_le_numeral: \<open>0 \<le> numeral n\<close>
  using dual_order.trans one_le_numeral zero_le_one by blast

lemma zero_less_numeral: \<open>0 < numeral n\<close>
  using less_linear not_numeral_less_one order.strict_trans zero_less_one by blast

lemma not_numeral_le_zero: \<open>\<not> numeral n \<le> 0\<close>
  by (simp add: not_le zero_less_numeral)

lemma not_numeral_less_zero: \<open>\<not> numeral n < 0\<close>
  by (simp add: not_less zero_le_numeral)

lemma one_of_nat_le_iff [simp]: \<open>1 \<le> of_nat k \<longleftrightarrow> 1 \<le> k\<close>
  using of_nat_le_iff [of 1] by simp

lemma numeral_nat_le_iff [simp]: \<open>numeral n \<le> of_nat k \<longleftrightarrow> numeral n \<le> k\<close>
  using of_nat_le_iff [of \<open>numeral n\<close>] by simp

lemma of_nat_le_1_iff [simp]: \<open>of_nat k \<le> 1 \<longleftrightarrow> k \<le> 1\<close>
  using of_nat_le_iff [of _ 1] by simp

lemma of_nat_le_numeral_iff [simp]: \<open>of_nat k \<le> numeral n \<longleftrightarrow> k \<le> numeral n\<close>
  using of_nat_le_iff [of _ \<open>numeral n\<close>] by simp

lemma one_of_nat_less_iff [simp]: \<open>1 < of_nat k \<longleftrightarrow> 1 < k\<close>
  using of_nat_less_iff [of 1] by simp

lemma numeral_nat_less_iff [simp]: \<open>numeral n < of_nat k \<longleftrightarrow> numeral n < k\<close>
  using of_nat_less_iff [of \<open>numeral n\<close>] by simp

lemma of_nat_less_1_iff [simp]: \<open>of_nat k < 1 \<longleftrightarrow> k < 1\<close>
  using of_nat_less_iff [of _ 1] by simp

lemma of_nat_less_numeral_iff [simp]: \<open>of_nat k < numeral n \<longleftrightarrow> k < numeral n\<close>
  using of_nat_less_iff [of _ \<open>numeral n\<close>] by simp

lemma of_nat_eq_numeral_iff [simp]: \<open>of_nat k = numeral n \<longleftrightarrow> k = numeral n\<close>
  using of_nat_eq_iff [of _ \<open>numeral n\<close>] by simp

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
  fixes min' :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  defines \<open>min' \<equiv> min\<close>
  shows
    \<open>min' 0 1 = 0\<close>
    \<open>min' 1 0 = 0\<close>
    \<open>min' 0 (numeral x) = 0\<close>
    \<open>min' (numeral x) 0 = 0\<close>
    \<open>min' 1 (numeral x) = 1\<close>
    \<open>min' (numeral x) 1 = 1\<close>
  by (simp_all add: min'_def min_def le_num_One_iff)

lemma max_0_1 [simp]:
  fixes max' :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  defines \<open>max' \<equiv> max\<close>
  shows
    \<open>max' 0 1 = 1\<close>
    \<open>max' 1 0 = 1\<close>
    \<open>max' 0 (numeral x) = numeral x\<close>
    \<open>max' (numeral x) 0 = numeral x\<close>
    \<open>max' 1 (numeral x) = numeral x\<close>
    \<open>max' (numeral x) 1 = numeral x\<close>
  by (simp_all add: max'_def max_def le_num_One_iff)

end

text \<open>Unfold \<open>min\<close> and \<open>max\<close> on numerals.\<close>

lemmas max_number_of [simp] =
  max_def [of \<open>numeral u\<close> \<open>numeral v\<close>]
  max_def [of \<open>numeral u\<close> \<open>- numeral v\<close>]
  max_def [of \<open>- numeral u\<close> \<open>numeral v\<close>]
  max_def [of \<open>- numeral u\<close> \<open>- numeral v\<close>] for u v

lemmas min_number_of [simp] =
  min_def [of \<open>numeral u\<close> \<open>numeral v\<close>]
  min_def [of \<open>numeral u\<close> \<open>- numeral v\<close>]
  min_def [of \<open>- numeral u\<close> \<open>numeral v\<close>]
  min_def [of \<open>- numeral u\<close> \<open>- numeral v\<close>] for u v


subsubsection \<open>Multiplication and negation: class \<open>ring_1\<close>\<close>

context ring_1
begin

subclass neg_numeral ..

lemma mult_neg_numeral_simps:
  \<open>- numeral m * - numeral n = numeral (m * n)\<close>
  \<open>- numeral m * numeral n = - numeral (m * n)\<close>
  \<open>numeral m * - numeral n = - numeral (m * n)\<close>
  by (simp_all only: mult_minus_left mult_minus_right minus_minus numeral_mult)

lemma mult_minus1 [simp]: \<open>- 1 * z = - z\<close>
  by (simp add: numeral.simps)

lemma mult_minus1_right [simp]: \<open>z * - 1 = - z\<close>
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

definition iszero :: \<open>'a \<Rightarrow> bool\<close>
  where \<open>iszero z \<longleftrightarrow> z = 0\<close>

lemma iszero_0 [simp]: \<open>iszero 0\<close>
  by (simp add: iszero_def)

lemma not_iszero_1 [simp]: \<open>\<not> iszero 1\<close>
  by (simp add: iszero_def)

lemma not_iszero_Numeral1: \<open>\<not> iszero Numeral1\<close>
  by (simp add: numeral_One)

lemma not_iszero_neg_1 [simp]: \<open>\<not> iszero (- 1)\<close>
  by (simp add: iszero_def)

lemma not_iszero_neg_Numeral1: \<open>\<not> iszero (- Numeral1)\<close>
  by (simp add: numeral_One)

lemma iszero_neg_numeral [simp]: \<open>iszero (- numeral w) \<longleftrightarrow> iszero (numeral w)\<close>
  unfolding iszero_def by (rule neg_equal_0_iff_equal)

lemma eq_iff_iszero_diff: \<open>x = y \<longleftrightarrow> iszero (x - y)\<close>
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
  \<open>numeral x = numeral y \<longleftrightarrow> iszero (sub x y)\<close>
  \<open>numeral x = - numeral y \<longleftrightarrow> iszero (numeral (x + y))\<close>
  \<open>- numeral x = numeral y \<longleftrightarrow> iszero (numeral (x + y))\<close>
  \<open>- numeral x = - numeral y \<longleftrightarrow> iszero (sub y x)\<close>
  \<open>numeral x = 1 \<longleftrightarrow> iszero (sub x One)\<close>
  \<open>1 = numeral y \<longleftrightarrow> iszero (sub One y)\<close>
  \<open>- numeral x = 1 \<longleftrightarrow> iszero (numeral (x + One))\<close>
  \<open>1 = - numeral y \<longleftrightarrow> iszero (numeral (One + y))\<close>
  \<open>numeral x = 0 \<longleftrightarrow> iszero (numeral x)\<close>
  \<open>0 = numeral y \<longleftrightarrow> iszero (numeral y)\<close>
  \<open>- numeral x = 0 \<longleftrightarrow> iszero (numeral x)\<close>
  \<open>0 = - numeral y \<longleftrightarrow> iszero (numeral y)\<close>
  unfolding eq_iff_iszero_diff diff_numeral_simps diff_numeral_special
  by simp_all

end


subsubsection \<open>Equality and negation: class \<open>ring_char_0\<close>\<close>

context ring_char_0
begin

lemma not_iszero_numeral [simp]: \<open>\<not> iszero (numeral w)\<close>
  by (simp add: iszero_def)

lemma neg_numeral_eq_iff: \<open>- numeral m = - numeral n \<longleftrightarrow> m = n\<close>
  by simp

lemma numeral_neq_neg_numeral: \<open>numeral m \<noteq> - numeral n\<close>
  by (simp add: eq_neg_iff_add_eq_0 numeral_plus_numeral)

lemma neg_numeral_neq_numeral: \<open>- numeral m \<noteq> numeral n\<close>
  by (rule numeral_neq_neg_numeral [symmetric])

lemma zero_neq_neg_numeral: \<open>0 \<noteq> - numeral n\<close>
  by simp

lemma neg_numeral_neq_zero: \<open>- numeral n \<noteq> 0\<close>
  by simp

lemma one_neq_neg_numeral: \<open>1 \<noteq> - numeral n\<close>
  using numeral_neq_neg_numeral [of One n] by (simp add: numeral_One)

lemma neg_numeral_neq_one: \<open>- numeral n \<noteq> 1\<close>
  using neg_numeral_neq_numeral [of n One] by (simp add: numeral_One)

lemma neg_one_neq_numeral: \<open>- 1 \<noteq> numeral n\<close>
  using neg_numeral_neq_numeral [of One n] by (simp add: numeral_One)

lemma numeral_neq_neg_one: \<open>numeral n \<noteq> - 1\<close>
  using numeral_neq_neg_numeral [of n One] by (simp add: numeral_One)

lemma neg_one_eq_numeral_iff: \<open>- 1 = - numeral n \<longleftrightarrow> n = One\<close>
  using neg_numeral_eq_iff [of One n] by (auto simp add: numeral_One)

lemma numeral_eq_neg_one_iff: \<open>- numeral n = - 1 \<longleftrightarrow> n = One\<close>
  using neg_numeral_eq_iff [of n One] by (auto simp add: numeral_One)

lemma neg_one_neq_zero: \<open>- 1 \<noteq> 0\<close>
  by simp

lemma zero_neq_neg_one: \<open>0 \<noteq> - 1\<close>
  by simp

lemma neg_one_neq_one: \<open>- 1 \<noteq> 1\<close>
  using neg_numeral_neq_numeral [of One One] by (simp only: numeral_One not_False_eq_True)

lemma one_neq_neg_one: \<open>1 \<noteq> - 1\<close>
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

lemma neg_numeral_le_iff: \<open>- numeral m \<le> - numeral n \<longleftrightarrow> n \<le> m\<close>
  by (simp only: neg_le_iff_le numeral_le_iff)

lemma neg_numeral_less_iff: \<open>- numeral m < - numeral n \<longleftrightarrow> n < m\<close>
  by (simp only: neg_less_iff_less numeral_less_iff)

lemma neg_numeral_less_zero: \<open>- numeral n < 0\<close>
  by (simp only: neg_less_0_iff_less zero_less_numeral)

lemma neg_numeral_le_zero: \<open>- numeral n \<le> 0\<close>
  by (simp only: neg_le_0_iff_le zero_le_numeral)

lemma not_zero_less_neg_numeral: \<open>\<not> 0 < - numeral n\<close>
  by (simp only: not_less neg_numeral_le_zero)

lemma not_zero_le_neg_numeral: \<open>\<not> 0 \<le> - numeral n\<close>
  by (simp only: not_le neg_numeral_less_zero)

lemma neg_numeral_less_numeral: \<open>- numeral m < numeral n\<close>
  using neg_numeral_less_zero zero_less_numeral by (rule less_trans)

lemma neg_numeral_le_numeral: \<open>- numeral m \<le> numeral n\<close>
  by (simp only: less_imp_le neg_numeral_less_numeral)

lemma not_numeral_less_neg_numeral: \<open>\<not> numeral m < - numeral n\<close>
  by (simp only: not_less neg_numeral_le_numeral)

lemma not_numeral_le_neg_numeral: \<open>\<not> numeral m \<le> - numeral n\<close>
  by (simp only: not_le neg_numeral_less_numeral)

lemma neg_numeral_less_one: \<open>- numeral m < 1\<close>
  by (rule neg_numeral_less_numeral [of m One, unfolded numeral_One])

lemma neg_numeral_le_one: \<open>- numeral m \<le> 1\<close>
  by (rule neg_numeral_le_numeral [of m One, unfolded numeral_One])

lemma not_one_less_neg_numeral: \<open>\<not> 1 < - numeral m\<close>
  by (simp only: not_less neg_numeral_le_one)

lemma not_one_le_neg_numeral: \<open>\<not> 1 \<le> - numeral m\<close>
  by (simp only: not_le neg_numeral_less_one)

lemma not_numeral_less_neg_one: \<open>\<not> numeral m < - 1\<close>
  using not_numeral_less_neg_numeral [of m One] by (simp add: numeral_One)

lemma not_numeral_le_neg_one: \<open>\<not> numeral m \<le> - 1\<close>
  using not_numeral_le_neg_numeral [of m One] by (simp add: numeral_One)

lemma neg_one_less_numeral: \<open>- 1 < numeral m\<close>
  using neg_numeral_less_numeral [of One m] by (simp add: numeral_One)

lemma neg_one_le_numeral: \<open>- 1 \<le> numeral m\<close>
  using neg_numeral_le_numeral [of One m] by (simp add: numeral_One)

lemma neg_numeral_less_neg_one_iff: \<open>- numeral m < - 1 \<longleftrightarrow> m \<noteq> One\<close>
  by (cases m) simp_all

lemma neg_numeral_le_neg_one: \<open>- numeral m \<le> - 1\<close>
  by simp

lemma not_neg_one_less_neg_numeral: \<open>\<not> - 1 < - numeral m\<close>
  by simp

lemma not_neg_one_le_neg_numeral_iff: \<open>\<not> - 1 \<le> - numeral m \<longleftrightarrow> m \<noteq> One\<close>
  by (cases m) simp_all

lemma sub_non_negative: \<open>sub n m \<ge> 0 \<longleftrightarrow> n \<ge> m\<close>
  by (simp only: sub_def le_diff_eq) simp

lemma sub_positive: \<open>sub n m > 0 \<longleftrightarrow> n > m\<close>
  by (simp only: sub_def less_diff_eq) simp

lemma sub_non_positive: \<open>sub n m \<le> 0 \<longleftrightarrow> n \<le> m\<close>
  by (simp only: sub_def diff_le_eq) simp

lemma sub_negative: \<open>sub n m < 0 \<longleftrightarrow> n < m\<close>
  by (simp only: sub_def diff_less_eq) simp

lemmas le_neg_numeral_simps [simp] =
  neg_numeral_le_iff
  neg_numeral_le_numeral not_numeral_le_neg_numeral
  neg_numeral_le_zero not_zero_le_neg_numeral
  neg_numeral_le_one not_one_le_neg_numeral
  neg_one_le_numeral not_numeral_le_neg_one
  neg_numeral_le_neg_one not_neg_one_le_neg_numeral_iff

lemma le_minus_one_simps [simp]:
  \<open>- 1 \<le> 0\<close>
  \<open>- 1 \<le> 1\<close>
  \<open>\<not> 0 \<le> - 1\<close>
  \<open>\<not> 1 \<le> - 1\<close>
  by simp_all

lemmas less_neg_numeral_simps [simp] =
  neg_numeral_less_iff
  neg_numeral_less_numeral not_numeral_less_neg_numeral
  neg_numeral_less_zero not_zero_less_neg_numeral
  neg_numeral_less_one not_one_less_neg_numeral
  neg_one_less_numeral not_numeral_less_neg_one
  neg_numeral_less_neg_one_iff not_neg_one_less_neg_numeral

lemma less_minus_one_simps [simp]:
  \<open>- 1 < 0\<close>
  \<open>- 1 < 1\<close>
  \<open>\<not> 0 < - 1\<close>
  \<open>\<not> 1 < - 1\<close>
  by (simp_all add: less_le)

lemma abs_numeral [simp]: \<open>\<bar>numeral n\<bar> = numeral n\<close>
  by simp

lemma abs_neg_numeral [simp]: \<open>\<bar>- numeral n\<bar> = numeral n\<close>
  by (simp only: abs_minus_cancel abs_numeral)

lemma abs_neg_one [simp]: \<open>\<bar>- 1\<bar> = 1\<close>
  by simp

end


subsubsection \<open>Natural numbers\<close>

lemma numeral_num_of_nat:
  \<open>numeral (num_of_nat n) = n\<close> if \<open>n > 0\<close>
  using that nat_of_num_numeral num_of_nat_inverse by simp

lemma Suc_1 [simp]: \<open>Suc 1 = 2\<close>
  unfolding Suc_eq_plus1 by (rule one_add_one)

lemma Suc_numeral [simp]: \<open>Suc (numeral n) = numeral (n + One)\<close>
  unfolding Suc_eq_plus1 by (rule numeral_plus_one)

definition pred_numeral :: \<open>num \<Rightarrow> nat\<close>
  where \<open>pred_numeral k = numeral k - 1\<close>

declare [[code drop: pred_numeral]]

lemma numeral_eq_Suc: \<open>numeral k = Suc (pred_numeral k)\<close>
  by (simp add: pred_numeral_def)

lemma eval_nat_numeral:
  \<open>numeral One = Suc 0\<close>
  \<open>numeral (Bit0 n) = Suc (numeral (BitM n))\<close>
  \<open>numeral (Bit1 n) = Suc (numeral (Bit0 n))\<close>
  by (simp_all add: numeral.simps BitM_plus_one)

lemma pred_numeral_simps [simp]:
  \<open>pred_numeral One = 0\<close>
  \<open>pred_numeral (Bit0 k) = numeral (BitM k)\<close>
  \<open>pred_numeral (Bit1 k) = numeral (Bit0 k)\<close>
  by (simp_all only: pred_numeral_def eval_nat_numeral diff_Suc_Suc diff_0)

lemma pred_numeral_inc [simp]:
  \<open>pred_numeral (inc k) = numeral k\<close>
  by (simp only: pred_numeral_def numeral_inc diff_add_inverse2)

lemma numeral_2_eq_2: \<open>2 = Suc (Suc 0)\<close>
  by (simp add: eval_nat_numeral)

lemma numeral_3_eq_3: \<open>3 = Suc (Suc (Suc 0))\<close>
  by (simp add: eval_nat_numeral)

lemma numeral_1_eq_Suc_0: \<open>Numeral1 = Suc 0\<close>
  by (simp only: numeral_One One_nat_def)

lemma Suc_nat_number_of_add: \<open>Suc (numeral v + n) = numeral (v + One) + n\<close>
  by simp

lemma numerals: \<open>Numeral1 = (1::nat)\<close> \<open>2 = Suc (Suc 0)\<close>
  by (rule numeral_One) (rule numeral_2_eq_2)

lemmas numeral_nat = eval_nat_numeral BitM.simps One_nat_def

text \<open>Comparisons involving \<^term>\<open>Suc\<close>.\<close>

lemma eq_numeral_Suc [simp]: \<open>numeral k = Suc n \<longleftrightarrow> pred_numeral k = n\<close>
  by (simp add: numeral_eq_Suc)

lemma Suc_eq_numeral [simp]: \<open>Suc n = numeral k \<longleftrightarrow> n = pred_numeral k\<close>
  by (simp add: numeral_eq_Suc)

lemma less_numeral_Suc [simp]: \<open>numeral k < Suc n \<longleftrightarrow> pred_numeral k < n\<close>
  by (simp add: numeral_eq_Suc)

lemma less_Suc_numeral [simp]: \<open>Suc n < numeral k \<longleftrightarrow> n < pred_numeral k\<close>
  by (simp add: numeral_eq_Suc)

lemma le_numeral_Suc [simp]: \<open>numeral k \<le> Suc n \<longleftrightarrow> pred_numeral k \<le> n\<close>
  by (simp add: numeral_eq_Suc)

lemma le_Suc_numeral [simp]: \<open>Suc n \<le> numeral k \<longleftrightarrow> n \<le> pred_numeral k\<close>
  by (simp add: numeral_eq_Suc)

lemma diff_Suc_numeral [simp]: \<open>Suc n - numeral k = n - pred_numeral k\<close>
  by (simp add: numeral_eq_Suc)

lemma diff_numeral_Suc [simp]: \<open>numeral k - Suc n = pred_numeral k - n\<close>
  by (simp add: numeral_eq_Suc)

lemma max_Suc_numeral [simp]: \<open>max (Suc n) (numeral k) = Suc (max n (pred_numeral k))\<close>
  by (simp add: numeral_eq_Suc)

lemma max_numeral_Suc [simp]: \<open>max (numeral k) (Suc n) = Suc (max (pred_numeral k) n)\<close>
  by (simp add: numeral_eq_Suc)

lemma min_Suc_numeral [simp]: \<open>min (Suc n) (numeral k) = Suc (min n (pred_numeral k))\<close>
  by (simp add: numeral_eq_Suc)

lemma min_numeral_Suc [simp]: \<open>min (numeral k) (Suc n) = Suc (min (pred_numeral k) n)\<close>
  by (simp add: numeral_eq_Suc)

text \<open>For \<^term>\<open>case_nat\<close> and \<^term>\<open>rec_nat\<close>.\<close>

lemma case_nat_numeral [simp]: \<open>case_nat a f (numeral v) = (let pv = pred_numeral v in f pv)\<close>
  by (simp add: numeral_eq_Suc)

lemma case_nat_add_eq_if [simp]:
  \<open>case_nat a f ((numeral v) + n) = (let pv = pred_numeral v in f (pv + n))\<close>
  by (simp add: numeral_eq_Suc)

lemma rec_nat_numeral [simp]:
  \<open>rec_nat a f (numeral v) = (let pv = pred_numeral v in f pv (rec_nat a f pv))\<close>
  by (simp add: numeral_eq_Suc Let_def)

lemma rec_nat_add_eq_if [simp]:
  \<open>rec_nat a f (numeral v + n) = (let pv = pred_numeral v in f (pv + n) (rec_nat a f (pv + n)))\<close>
  by (simp add: numeral_eq_Suc Let_def)

text \<open>Case analysis on \<^term>\<open>n < 2\<close>.\<close>
lemma less_2_cases: \<open>n < 2 \<Longrightarrow> n = 0 \<or> n = Suc 0\<close>
  by (auto simp add: numeral_2_eq_2)

lemma less_2_cases_iff: \<open>n < 2 \<longleftrightarrow> n = 0 \<or> n = Suc 0\<close>
  by (auto simp add: numeral_2_eq_2)

text \<open>Removal of Small Numerals: 0, 1 and (in additive positions) 2.\<close>
text \<open>bh: Are these rules really a good idea? LCP: well, it already happens for 0 and 1!\<close>

lemma add_2_eq_Suc [simp]: \<open>2 + n = Suc (Suc n)\<close>
  by simp

lemma add_2_eq_Suc' [simp]: \<open>n + 2 = Suc (Suc n)\<close>
  by simp

text \<open>Can be used to eliminate long strings of Sucs, but not by default.\<close>
lemma Suc3_eq_add_3: \<open>Suc (Suc (Suc n)) = 3 + n\<close>
  by simp

lemmas nat_1_add_1 = one_add_one [where 'a=nat] (* legacy *)

context semiring_numeral
begin

lemma numeral_add_unfold_funpow:
  \<open>numeral k + a = ((+) 1 ^^ numeral k) a\<close>
proof (rule sym, induction k arbitrary: a)
  case One
  then show ?case
    by (simp add: Num.numeral_One numeral_One)
next
  case (Bit0 k)
  then show ?case
    by (simp add: Num.numeral_Bit0 numeral_Bit0 ac_simps funpow_add)
next
  case (Bit1 k)
  then show ?case
    by (simp add: Num.numeral_Bit1 numeral_Bit1 ac_simps funpow_add)
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
  have \<open>((=) ===> R) (\<lambda>k. ((+) 1 ^^ numeral k) 0) (\<lambda>k. ((+) 1 ^^ numeral k) 0)\<close>
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

lemma half_gt_zero_iff: \<open>0 < a / 2 \<longleftrightarrow> 0 < a\<close>
  by (auto simp add: field_simps)

lemma half_gt_zero [simp]: \<open>0 < a \<Longrightarrow> 0 < a / 2\<close>
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

lemmas distrib_right_numeral [simp] = distrib_right [of _ _ \<open>numeral v\<close>] for v
lemmas distrib_left_numeral [simp] = distrib_left [of \<open>numeral v\<close>] for v
lemmas left_diff_distrib_numeral [simp] = left_diff_distrib [of _ _ \<open>numeral v\<close>] for v
lemmas right_diff_distrib_numeral [simp] = right_diff_distrib [of \<open>numeral v\<close>] for v

text \<open>These are actually for fields, like real\<close>

lemmas zero_less_divide_iff_numeral [simp, no_atp] = zero_less_divide_iff [of \<open>numeral w\<close>] for w
lemmas divide_less_0_iff_numeral [simp, no_atp] = divide_less_0_iff [of \<open>numeral w\<close>] for w
lemmas zero_le_divide_iff_numeral [simp, no_atp] = zero_le_divide_iff [of \<open>numeral w\<close>] for w
lemmas divide_le_0_iff_numeral [simp, no_atp] = divide_le_0_iff [of \<open>numeral w\<close>] for w

text \<open>Replaces \<open>inverse #nn\<close> by \<open>1/#nn\<close>.  It looks
  strange, but then other simprocs simplify the quotient.\<close>

lemmas inverse_eq_divide_numeral [simp] =
  inverse_eq_divide [of \<open>numeral w\<close>] for w

lemmas inverse_eq_divide_neg_numeral [simp] =
  inverse_eq_divide [of \<open>- numeral w\<close>] for w

text \<open>These laws simplify inequalities, moving unary minus from a term
  into the literal.\<close>

lemmas equation_minus_iff_numeral [no_atp] =
  equation_minus_iff [of \<open>numeral v\<close>] for v

lemmas minus_equation_iff_numeral [no_atp] =
  minus_equation_iff [of _ \<open>numeral v\<close>] for v

lemmas le_minus_iff_numeral [no_atp] =
  le_minus_iff [of \<open>numeral v\<close>] for v

lemmas minus_le_iff_numeral [no_atp] =
  minus_le_iff [of _ \<open>numeral v\<close>] for v

lemmas less_minus_iff_numeral [no_atp] =
  less_minus_iff [of \<open>numeral v\<close>] for v

lemmas minus_less_iff_numeral [no_atp] =
  minus_less_iff [of _ \<open>numeral v\<close>] for v

(* FIXME maybe simproc *)

text \<open>Cancellation of constant factors in comparisons (\<open><\<close> and \<open>\<le>\<close>)\<close>

lemmas mult_less_cancel_left_numeral [simp, no_atp] = mult_less_cancel_left [of \<open>numeral v\<close>] for v
lemmas mult_less_cancel_right_numeral [simp, no_atp] = mult_less_cancel_right [of _ \<open>numeral v\<close>] for v
lemmas mult_le_cancel_left_numeral [simp, no_atp] = mult_le_cancel_left [of \<open>numeral v\<close>] for v
lemmas mult_le_cancel_right_numeral [simp, no_atp] = mult_le_cancel_right [of _ \<open>numeral v\<close>] for v

text \<open>Multiplying out constant divisors in comparisons (\<open><\<close>, \<open>\<le>\<close> and \<open>=\<close>)\<close>

named_theorems divide_const_simps \<open>simplification rules to simplify comparisons involving constant divisors\<close>

lemmas le_divide_eq_numeral1 [simp,divide_const_simps] =
  pos_le_divide_eq [of \<open>numeral w\<close>, OF zero_less_numeral]
  neg_le_divide_eq [of \<open>- numeral w\<close>, OF neg_numeral_less_zero] for w

lemmas divide_le_eq_numeral1 [simp,divide_const_simps] =
  pos_divide_le_eq [of \<open>numeral w\<close>, OF zero_less_numeral]
  neg_divide_le_eq [of \<open>- numeral w\<close>, OF neg_numeral_less_zero] for w

lemmas less_divide_eq_numeral1 [simp,divide_const_simps] =
  pos_less_divide_eq [of \<open>numeral w\<close>, OF zero_less_numeral]
  neg_less_divide_eq [of \<open>- numeral w\<close>, OF neg_numeral_less_zero] for w

lemmas divide_less_eq_numeral1 [simp,divide_const_simps] =
  pos_divide_less_eq [of \<open>numeral w\<close>, OF zero_less_numeral]
  neg_divide_less_eq [of \<open>- numeral w\<close>, OF neg_numeral_less_zero] for w

lemmas eq_divide_eq_numeral1 [simp,divide_const_simps] =
  eq_divide_eq [of _ _ \<open>numeral w\<close>]
  eq_divide_eq [of _ _ \<open>- numeral w\<close>] for w

lemmas divide_eq_eq_numeral1 [simp,divide_const_simps] =
  divide_eq_eq [of _ \<open>numeral w\<close>]
  divide_eq_eq [of _ \<open>- numeral w\<close>] for w


subsubsection \<open>Optional Simplification Rules Involving Constants\<close>

text \<open>Simplify quotients that are compared with a literal constant.\<close>

lemmas le_divide_eq_numeral [divide_const_simps] =
  le_divide_eq [of \<open>numeral w\<close>]
  le_divide_eq [of \<open>- numeral w\<close>] for w

lemmas divide_le_eq_numeral [divide_const_simps] =
  divide_le_eq [of _ _ \<open>numeral w\<close>]
  divide_le_eq [of _ _ \<open>- numeral w\<close>] for w

lemmas less_divide_eq_numeral [divide_const_simps] =
  less_divide_eq [of \<open>numeral w\<close>]
  less_divide_eq [of \<open>- numeral w\<close>] for w

lemmas divide_less_eq_numeral [divide_const_simps] =
  divide_less_eq [of _ _ \<open>numeral w\<close>]
  divide_less_eq [of _ _ \<open>- numeral w\<close>] for w

lemmas eq_divide_eq_numeral [divide_const_simps] =
  eq_divide_eq [of \<open>numeral w\<close>]
  eq_divide_eq [of \<open>- numeral w\<close>] for w

lemmas divide_eq_eq_numeral [divide_const_simps] =
  divide_eq_eq [of _ _ \<open>numeral w\<close>]
  divide_eq_eq [of _ _ \<open>- numeral w\<close>] for w

text \<open>Not good as automatic simprules because they cause case splits.\<close>

lemmas [divide_const_simps] =
  le_divide_eq_1 divide_le_eq_1 less_divide_eq_1 divide_less_eq_1


subsection \<open>Setting up simprocs\<close>

lemma mult_numeral_1: \<open>Numeral1 * a = a\<close>
  for a :: \<open>'a::semiring_numeral\<close>
  by simp

lemma mult_numeral_1_right: \<open>a * Numeral1 = a\<close>
  for a :: \<open>'a::semiring_numeral\<close>
  by simp

lemma divide_numeral_1: \<open>a / Numeral1 = a\<close>
  for a :: \<open>'a::field\<close>
  by simp

lemma inverse_numeral_1: \<open>inverse Numeral1 = (Numeral1::'a::division_ring)\<close>
  by simp

text \<open>
  Theorem lists for the cancellation simprocs. The use of a binary
  numeral for 1 reduces the number of special cases.
\<close>

lemma mult_1s_semiring_numeral:
  \<open>Numeral1 * a = a\<close>
  \<open>a * Numeral1 = a\<close>
  for a :: \<open>'a::semiring_numeral\<close>
  by simp_all

lemma mult_1s_ring_1:
  \<open>- Numeral1 * b = - b\<close>
  \<open>b * - Numeral1 = - b\<close>
  for b :: \<open>'a::ring_1\<close>
  by simp_all

lemmas mult_1s = mult_1s_semiring_numeral mult_1s_ring_1

setup \<open>
  Reorient_Proc.add
    (fn Const (\<^const_name>\<open>numeral\<close>, _) $ _ => true
      | Const (\<^const_name>\<open>uminus\<close>, _) $ (Const (\<^const_name>\<open>numeral\<close>, _) $ _) => true
      | _ => false)
\<close>

simproc_setup reorient_numeral (\<open>numeral w = x\<close> | \<open>- numeral w = y\<close>) =
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

lemma Let_numeral [simp]: \<open>Let (numeral v) f = f (numeral v)\<close>
  \<comment> \<open>Unfold all \<open>let\<close>s involving constants\<close>
  unfolding Let_def ..

lemma Let_neg_numeral [simp]: \<open>Let (- numeral v) f = f (- numeral v)\<close>
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

lemma add_numeral_left [simp]: \<open>numeral v + (numeral w + z) = (numeral(v + w) + z)\<close>
  by (simp_all add: add.assoc [symmetric])

lemma add_neg_numeral_left [simp]:
  \<open>numeral v + (- numeral w + y) = (sub v w + y)\<close>
  \<open>- numeral v + (numeral w + y) = (sub w v + y)\<close>
  \<open>- numeral v + (- numeral w + y) = (- numeral(v + w) + y)\<close>
  by (simp_all add: add.assoc [symmetric])

lemma mult_numeral_left_semiring_numeral:
  \<open>numeral v * (numeral w * z) = (numeral(v * w) * z :: 'a::semiring_numeral)\<close>
  by (simp add: mult.assoc [symmetric])

lemma mult_numeral_left_ring_1:
  \<open>- numeral v * (numeral w * y) = (- numeral(v * w) * y :: 'a::ring_1)\<close>
  \<open>numeral v * (- numeral w * y) = (- numeral(v * w) * y :: 'a::ring_1)\<close>
  \<open>- numeral v * (- numeral w * y) = (numeral(v * w) * y :: 'a::ring_1)\<close>
  by (simp_all add: mult.assoc [symmetric])

lemmas mult_numeral_left [simp] =
  mult_numeral_left_semiring_numeral
  mult_numeral_left_ring_1



subsection \<open>Code module namespace\<close>

code_identifier
  code_module Num \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

subsection \<open>Printing of evaluated natural numbers as numerals\<close>

lemma [code_post]:
  \<open>Suc 0 = 1\<close>
  \<open>Suc 1 = 2\<close>
  \<open>Suc (numeral n) = numeral (inc n)\<close>
  by (simp_all add: numeral_inc)

lemmas [code_post] = inc.simps


subsection \<open>More on auxiliary conversion\<close>

context semiring_1
begin

lemma num_of_nat_numeral_eq [simp]:
  \<open>num_of_nat (numeral q) = q\<close>
  by (simp flip: nat_of_num_numeral add: nat_of_num_inverse)

lemma numeral_num_of_nat_unfold:
  \<open>numeral (num_of_nat n) = (if n = 0 then 1 else of_nat n)\<close>
  apply (simp only: of_nat_numeral [symmetric, of \<open>num_of_nat n\<close>] flip: nat_of_num_numeral)
  apply (auto simp add: num_of_nat_inverse)
  done

end


hide_const (open) One Bit0 Bit1 BitM inc pow sqr sub dbl dbl_inc dbl_dec

end
