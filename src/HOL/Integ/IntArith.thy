(*  Title:      HOL/Integ/IntArith.thy
    ID:         $Id$
    Authors:    Larry Paulson and Tobias Nipkow
*)

header {* Integer arithmetic *}

theory IntArith
imports Numeral
uses ("int_arith1.ML")
begin

text{*Duplicate: can't understand why it's necessary*}
declare numeral_0_eq_0 [simp]


subsection{*Instantiating Binary Arithmetic for the Integers*}

instance
  int :: number ..

defs (overloaded)
  int_number_of_def: "(number_of w :: int) == of_int (Rep_Bin w)"
    --{*the type constraint is essential!*}

instance int :: number_ring
by (intro_classes, simp add: int_number_of_def) 


subsection{*Inequality Reasoning for the Arithmetic Simproc*}

lemma add_numeral_0: "Numeral0 + a = (a::'a::number_ring)"
by simp 

lemma add_numeral_0_right: "a + Numeral0 = (a::'a::number_ring)"
by simp

lemma mult_numeral_1: "Numeral1 * a = (a::'a::number_ring)"
by simp 

lemma mult_numeral_1_right: "a * Numeral1 = (a::'a::number_ring)"
by simp

text{*Theorem lists for the cancellation simprocs. The use of binary numerals
for 0 and 1 reduces the number of special cases.*}

lemmas add_0s = add_numeral_0 add_numeral_0_right
lemmas mult_1s = mult_numeral_1 mult_numeral_1_right 
                 mult_minus1 mult_minus1_right


subsection{*Special Arithmetic Rules for Abstract 0 and 1*}

text{*Arithmetic computations are defined for binary literals, which leaves 0
and 1 as special cases. Addition already has rules for 0, but not 1.
Multiplication and unary minus already have rules for both 0 and 1.*}


lemma binop_eq: "[|f x y = g x y; x = x'; y = y'|] ==> f x' y' = g x' y'"
by simp


lemmas add_number_of_eq = number_of_add [symmetric]

text{*Allow 1 on either or both sides*}
lemma one_add_one_is_two: "1 + 1 = (2::'a::number_ring)"
by (simp del: numeral_1_eq_1 add: numeral_1_eq_1 [symmetric] add_number_of_eq)

lemmas add_special =
    one_add_one_is_two
    binop_eq [of "op +", OF add_number_of_eq numeral_1_eq_1 refl, standard]
    binop_eq [of "op +", OF add_number_of_eq refl numeral_1_eq_1, standard]

text{*Allow 1 on either or both sides (1-1 already simplifies to 0)*}
lemmas diff_special =
    binop_eq [of "op -", OF diff_number_of_eq numeral_1_eq_1 refl, standard]
    binop_eq [of "op -", OF diff_number_of_eq refl numeral_1_eq_1, standard]

text{*Allow 0 or 1 on either side with a binary numeral on the other*}
lemmas eq_special =
    binop_eq [of "op =", OF eq_number_of_eq numeral_0_eq_0 refl, standard]
    binop_eq [of "op =", OF eq_number_of_eq numeral_1_eq_1 refl, standard]
    binop_eq [of "op =", OF eq_number_of_eq refl numeral_0_eq_0, standard]
    binop_eq [of "op =", OF eq_number_of_eq refl numeral_1_eq_1, standard]

text{*Allow 0 or 1 on either side with a binary numeral on the other*}
lemmas less_special =
  binop_eq [of "op <", OF less_number_of_eq_neg numeral_0_eq_0 refl, standard]
  binop_eq [of "op <", OF less_number_of_eq_neg numeral_1_eq_1 refl, standard]
  binop_eq [of "op <", OF less_number_of_eq_neg refl numeral_0_eq_0, standard]
  binop_eq [of "op <", OF less_number_of_eq_neg refl numeral_1_eq_1, standard]

text{*Allow 0 or 1 on either side with a binary numeral on the other*}
lemmas le_special =
    binop_eq [of "op \<le>", OF le_number_of_eq numeral_0_eq_0 refl, standard]
    binop_eq [of "op \<le>", OF le_number_of_eq numeral_1_eq_1 refl, standard]
    binop_eq [of "op \<le>", OF le_number_of_eq refl numeral_0_eq_0, standard]
    binop_eq [of "op \<le>", OF le_number_of_eq refl numeral_1_eq_1, standard]

lemmas arith_special = 
       add_special diff_special eq_special less_special le_special


use "int_arith1.ML"
setup int_arith_setup


subsection{*Lemmas About Small Numerals*}

lemma of_int_m1 [simp]: "of_int -1 = (-1 :: 'a :: number_ring)"
proof -
  have "(of_int -1 :: 'a) = of_int (- 1)" by simp
  also have "... = - of_int 1" by (simp only: of_int_minus)
  also have "... = -1" by simp
  finally show ?thesis .
qed

lemma abs_minus_one [simp]: "abs (-1) = (1::'a::{ordered_idom,number_ring})"
by (simp add: abs_if)

lemma abs_power_minus_one [simp]:
     "abs(-1 ^ n) = (1::'a::{ordered_idom,number_ring,recpower})"
by (simp add: power_abs)

lemma of_int_number_of_eq:
     "of_int (number_of v) = (number_of v :: 'a :: number_ring)"
by (simp add: number_of_eq) 

text{*Lemmas for specialist use, NOT as default simprules*}
lemma mult_2: "2 * z = (z+z::'a::number_ring)"
proof -
  have "2*z = (1 + 1)*z" by simp
  also have "... = z+z" by (simp add: left_distrib)
  finally show ?thesis .
qed

lemma mult_2_right: "z * 2 = (z+z::'a::number_ring)"
by (subst mult_commute, rule mult_2)


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


subsection{*The Functions @{term nat} and @{term int}*}

text{*Simplify the terms @{term "int 0"}, @{term "int(Suc 0)"} and
  @{term "w + - z"}*}
declare Zero_int_def [symmetric, simp]
declare One_int_def [symmetric, simp]

text{*cooper.ML refers to this theorem*}
lemmas diff_int_def_symmetric = diff_int_def [symmetric, simp]

lemma nat_0: "nat 0 = 0"
by (simp add: nat_eq_iff)

lemma nat_1: "nat 1 = Suc 0"
by (subst nat_eq_iff, simp)

lemma nat_2: "nat 2 = Suc (Suc 0)"
by (subst nat_eq_iff, simp)

lemma one_less_nat_eq [simp]: "(Suc 0 < nat z) = (1 < z)"
apply (insert zless_nat_conj [of 1 z])
apply (auto simp add: nat_1)
done

text{*This simplifies expressions of the form @{term "int n = z"} where
      z is an integer literal.*}
lemmas int_eq_iff_number_of = int_eq_iff [of _ "number_of v", standard]
declare int_eq_iff_number_of [simp]


lemma split_nat [arith_split]:
  "P(nat(i::int)) = ((\<forall>n. i = int n \<longrightarrow> P n) & (i < 0 \<longrightarrow> P 0))"
  (is "?P = (?L & ?R)")
proof (cases "i < 0")
  case True thus ?thesis by simp
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


(*Analogous to zadd_int*)
lemma zdiff_int: "n \<le> m ==> int m - int n = int (m-n)" 
by (induct m n rule: diff_induct, simp_all)

lemma nat_mult_distrib: "(0::int) \<le> z ==> nat (z*z') = nat z * nat z'"
apply (case_tac "0 \<le> z'")
apply (rule inj_int [THEN injD])
apply (simp add: int_mult zero_le_mult_iff)
apply (simp add: mult_le_0_iff)
done

lemma nat_mult_distrib_neg: "z \<le> (0::int) ==> nat(z*z') = nat(-z) * nat(-z')"
apply (rule trans)
apply (rule_tac [2] nat_mult_distrib, auto)
done

lemma nat_abs_mult_distrib: "nat (abs (w * z)) = nat (abs w) * nat (abs z)"
apply (case_tac "z=0 | w=0")
apply (auto simp add: abs_if nat_mult_distrib [symmetric] 
                      nat_mult_distrib_neg [symmetric] mult_less_0_iff)
done


subsubsection "Induction principles for int"

                     (* `set:int': dummy construction *)
theorem int_ge_induct[case_names base step,induct set:int]:
  assumes ge: "k \<le> (i::int)" and
        base: "P(k)" and
        step: "\<And>i. \<lbrakk>k \<le> i; P i\<rbrakk> \<Longrightarrow> P(i+1)"
  shows "P i"
proof -
  { fix n have "\<And>i::int. n = nat(i-k) \<Longrightarrow> k \<le> i \<Longrightarrow> P i"
    proof (induct n)
      case 0
      hence "i = k" by arith
      thus "P i" using base by simp
    next
      case (Suc n)
      hence "n = nat((i - 1) - k)" by arith
      moreover
      have ki1: "k \<le> i - 1" using Suc.prems by arith
      ultimately
      have "P(i - 1)" by(rule Suc.hyps)
      from step[OF ki1 this] show ?case by simp
    qed
  }
  with ge show ?thesis by fast
qed

                     (* `set:int': dummy construction *)
theorem int_gr_induct[case_names base step,induct set:int]:
  assumes gr: "k < (i::int)" and
        base: "P(k+1)" and
        step: "\<And>i. \<lbrakk>k < i; P i\<rbrakk> \<Longrightarrow> P(i+1)"
  shows "P i"
apply(rule int_ge_induct[of "k + 1"])
  using gr apply arith
 apply(rule base)
apply (rule step, simp+)
done

theorem int_le_induct[consumes 1,case_names base step]:
  assumes le: "i \<le> (k::int)" and
        base: "P(k)" and
        step: "\<And>i. \<lbrakk>i \<le> k; P i\<rbrakk> \<Longrightarrow> P(i - 1)"
  shows "P i"
proof -
  { fix n have "\<And>i::int. n = nat(k-i) \<Longrightarrow> i \<le> k \<Longrightarrow> P i"
    proof (induct n)
      case 0
      hence "i = k" by arith
      thus "P i" using base by simp
    next
      case (Suc n)
      hence "n = nat(k - (i+1))" by arith
      moreover
      have ki1: "i + 1 \<le> k" using Suc.prems by arith
      ultimately
      have "P(i+1)" by(rule Suc.hyps)
      from step[OF ki1 this] show ?case by simp
    qed
  }
  with le show ?thesis by fast
qed

theorem int_less_induct [consumes 1,case_names base step]:
  assumes less: "(i::int) < k" and
        base: "P(k - 1)" and
        step: "\<And>i. \<lbrakk>i < k; P i\<rbrakk> \<Longrightarrow> P(i - 1)"
  shows "P i"
apply(rule int_le_induct[of _ "k - 1"])
  using less apply arith
 apply(rule base)
apply (rule step, simp+)
done

subsection{*Intermediate value theorems*}

lemma int_val_lemma:
     "(\<forall>i<n::nat. abs(f(i+1) - f i) \<le> 1) -->  
      f 0 \<le> k --> k \<le> f n --> (\<exists>i \<le> n. f i = (k::int))"
apply (induct_tac "n", simp)
apply (intro strip)
apply (erule impE, simp)
apply (erule_tac x = n in allE, simp)
apply (case_tac "k = f (n+1) ")
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
apply simp
apply (erule impE)
 apply (intro strip)
 apply (erule_tac x = "i+m" in allE, arith)
apply (erule exE)
apply (rule_tac x = "i+m" in exI, arith)
done


subsection{*Products and 1, by T. M. Rasmussen*}

lemma zabs_less_one_iff [simp]: "(\<bar>z\<bar> < 1) = (z = (0::int))"
by arith

lemma abs_zmult_eq_1: "(\<bar>m * n\<bar> = 1) ==> \<bar>m\<bar> = (1::int)"
apply (case_tac "\<bar>n\<bar>=1") 
apply (simp add: abs_mult) 
apply (rule ccontr) 
apply (auto simp add: linorder_neq_iff abs_mult) 
apply (subgoal_tac "2 \<le> \<bar>m\<bar> & 2 \<le> \<bar>n\<bar>")
 prefer 2 apply arith 
apply (subgoal_tac "2*2 \<le> \<bar>m\<bar> * \<bar>n\<bar>", simp) 
apply (rule mult_mono, auto) 
done

lemma pos_zmult_eq_1_iff_lemma: "(m * n = 1) ==> m = (1::int) | m = -1"
by (insert abs_zmult_eq_1 [of m n], arith)

lemma pos_zmult_eq_1_iff: "0 < (m::int) ==> (m * n = 1) = (m = 1 & n = 1)"
apply (auto dest: pos_zmult_eq_1_iff_lemma) 
apply (simp add: mult_commute [of m]) 
apply (frule pos_zmult_eq_1_iff_lemma, auto) 
done

lemma zmult_eq_1_iff: "(m*n = (1::int)) = ((m = 1 & n = 1) | (m = -1 & n = -1))"
apply (rule iffI) 
 apply (frule pos_zmult_eq_1_iff_lemma)
 apply (simp add: mult_commute [of m]) 
 apply (frule pos_zmult_eq_1_iff_lemma, auto) 
done

ML
{*
val zle_diff1_eq = thm "zle_diff1_eq";
val zle_add1_eq_le = thm "zle_add1_eq_le";
val nonneg_eq_int = thm "nonneg_eq_int";
val abs_minus_one = thm "abs_minus_one";
val of_int_number_of_eq = thm"of_int_number_of_eq";
val nat_eq_iff = thm "nat_eq_iff";
val nat_eq_iff2 = thm "nat_eq_iff2";
val nat_less_iff = thm "nat_less_iff";
val int_eq_iff = thm "int_eq_iff";
val nat_0 = thm "nat_0";
val nat_1 = thm "nat_1";
val nat_2 = thm "nat_2";
val nat_less_eq_zless = thm "nat_less_eq_zless";
val nat_le_eq_zle = thm "nat_le_eq_zle";

val nat_intermed_int_val = thm "nat_intermed_int_val";
val pos_zmult_eq_1_iff = thm "pos_zmult_eq_1_iff";
val zmult_eq_1_iff = thm "zmult_eq_1_iff";
val nat_add_distrib = thm "nat_add_distrib";
val nat_diff_distrib = thm "nat_diff_distrib";
val nat_mult_distrib = thm "nat_mult_distrib";
val nat_mult_distrib_neg = thm "nat_mult_distrib_neg";
val nat_abs_mult_distrib = thm "nat_abs_mult_distrib";
*}

end
