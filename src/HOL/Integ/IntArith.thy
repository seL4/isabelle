(*  Title:      HOL/Integ/IntArith.thy
    ID:         $Id$
    Authors:    Larry Paulson and Tobias Nipkow
*)

header {* Integer arithmetic *}

theory IntArith = Bin
files ("int_arith1.ML"):

use "int_arith1.ML"
setup int_arith_setup

lemma zle_diff1_eq [simp]: "(w <= z - (1::int)) = (w<(z::int))"
by arith

lemma zle_add1_eq_le [simp]: "(w < z + 1) = (w<=(z::int))"
by arith

lemma zadd_left_cancel0 [simp]: "(z = z + w) = (w = (0::int))"
by arith

subsection{*Results about @{term nat}*}

lemma nonneg_eq_int: "[| 0 <= z;  !!m. z = int m ==> P |] ==> P"
by (blast dest: nat_0_le sym)

lemma nat_eq_iff: "(nat w = m) = (if 0 <= w then w = int m else m=0)"
by auto

lemma nat_eq_iff2: "(m = nat w) = (if 0 <= w then w = int m else m=0)"
by auto

lemma nat_less_iff: "0 <= w ==> (nat w < m) = (w < int m)"
apply (rule iffI)
apply (erule nat_0_le [THEN subst])
apply (simp_all del: zless_int add: zless_int [symmetric]) 
done

lemma int_eq_iff: "(int m = z) = (m = nat z & 0 <= z)"
by (auto simp add: nat_eq_iff2)


(*Users don't want to see (int 0), int(Suc 0) or w + - z*)
declare Zero_int_def [symmetric, simp]
declare One_int_def [symmetric, simp]

text{*cooper.ML refers to this theorem*}
lemmas zdiff_def_symmetric = zdiff_def [symmetric, simp]

lemma nat_0: "nat 0 = 0"
by (simp add: nat_eq_iff)

lemma nat_1: "nat 1 = Suc 0"
by (subst nat_eq_iff, simp)

lemma nat_2: "nat 2 = Suc (Suc 0)"
by (subst nat_eq_iff, simp)

lemma nat_less_eq_zless: "0 <= w ==> (nat w < nat z) = (w<z)"
apply (case_tac "neg z")
apply (auto simp add: nat_less_iff)
apply (auto intro: zless_trans simp add: neg_eq_less_0 zle_def)
done

lemma nat_le_eq_zle: "0 < w | 0 <= z ==> (nat w <= nat z) = (w<=z)"
by (auto simp add: linorder_not_less [symmetric] zless_nat_conj)

subsection{*@{term abs}: Absolute Value, as an Integer*}

(* Simpler: use zabs_def as rewrite rule
   but arith_tac is not parameterized by such simp rules
*)

lemma zabs_split: "P(abs(i::int)) = ((0 <= i --> P i) & (i < 0 --> P(-i)))"
by (simp add: zabs_def)

lemma zero_le_zabs [iff]: "0 <= abs (z::int)"
by (simp add: zabs_def)


text{*This simplifies expressions of the form @{term "int n = z"} where
      z is an integer literal.*}
declare int_eq_iff [of _ "number_of v", standard, simp]

declare zabs_split [arith_split]

lemma zabs_eq_iff:
    "(abs (z::int) = w) = (z = w \<and> 0 <= z \<or> z = -w \<and> z < 0)"
  by (auto simp add: zabs_def)

lemma int_nat_eq [simp]: "int (nat z) = (if 0 \<le> z then z else 0)"
  by simp

lemma split_nat[arith_split]:
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

subsubsection "Induction principles for int"

                     (* `set:int': dummy construction *)
theorem int_ge_induct[case_names base step,induct set:int]:
  assumes ge: "k \<le> (i::int)" and
        base: "P(k)" and
        step: "\<And>i. \<lbrakk>k \<le> i; P i\<rbrakk> \<Longrightarrow> P(i+1)"
  shows "P i"
proof -
  { fix n have "\<And>i::int. n = nat(i-k) \<Longrightarrow> k <= i \<Longrightarrow> P i"
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
  from this ge show ?thesis by fast
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
  { fix n have "\<And>i::int. n = nat(k-i) \<Longrightarrow> i <= k \<Longrightarrow> P i"
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
  from this le show ?thesis by fast
qed

theorem int_less_induct[consumes 1,case_names base step]:
  assumes less: "(i::int) < k" and
        base: "P(k - 1)" and
        step: "\<And>i. \<lbrakk>i < k; P i\<rbrakk> \<Longrightarrow> P(i - 1)"
  shows "P i"
apply(rule int_le_induct[of _ "k - 1"])
  using less apply arith
 apply(rule base)
apply (rule step, simp+)
done

subsection{*Simple Equations*}

lemma int_diff_minus_eq [simp]: "x - - y = x + (y::int)"
by simp

lemma abs_abs [simp]: "abs(abs(x::int)) = abs(x)"
by arith

lemma abs_minus [simp]: "abs(-(x::int)) = abs(x)"
by arith

lemma triangle_ineq: "abs(x+y) <= abs(x) + abs(y::int)"
by arith


subsection{*Intermediate value theorems*}

lemma int_val_lemma:
     "(\<forall>i<n::nat. abs(f(i+1) - f i) \<le> 1) -->  
      f 0 \<le> k --> k \<le> f n --> (\<exists>i \<le> n. f i = (k::int))"
apply (induct_tac "n")
 apply (simp (no_asm_simp))
apply (intro strip)
apply (erule impE, simp)
apply (erule_tac x = n in allE, simp)
apply (case_tac "k = f (n+1) ")
 apply force
apply (erule impE)
 apply (simp add: zabs_def split add: split_if_asm)
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


subsection{*Some convenient biconditionals for products of signs*}

lemma zmult_pos: "[| (0::int) < i; 0 < j |] ==> 0 < i*j"
by (drule zmult_zless_mono1, auto)

lemma zmult_neg: "[| i < (0::int); j < 0 |] ==> 0 < i*j"
by (drule zmult_zless_mono1_neg, auto)

lemma zmult_pos_neg: "[| (0::int) < i; j < 0 |] ==> i*j < 0"
by (drule zmult_zless_mono1_neg, auto)

lemma int_0_less_mult_iff: "((0::int) < x*y) = (0 < x & 0 < y | x < 0 & y < 0)"
apply (auto simp add: order_le_less linorder_not_less zmult_pos zmult_neg)
apply (rule_tac [!] ccontr)
apply (auto simp add: order_le_less linorder_not_less)
apply (erule_tac [!] rev_mp)
apply (drule_tac [!] zmult_pos_neg)
apply (auto dest: order_less_not_sym simp add: zmult_commute)
done

lemma int_0_le_mult_iff: "((0::int) \<le> x*y) = (0 \<le> x & 0 \<le> y | x \<le> 0 & y \<le> 0)"
by (auto simp add: order_le_less linorder_not_less int_0_less_mult_iff)

lemma zmult_less_0_iff: "(x*y < (0::int)) = (0 < x & y < 0 | x < 0 & 0 < y)"
by (auto simp add: int_0_le_mult_iff linorder_not_le [symmetric])

lemma zmult_le_0_iff: "(x*y \<le> (0::int)) = (0 \<le> x & y \<le> 0 | x \<le> 0 & 0 \<le> y)"
by (auto dest: order_less_not_sym simp add: int_0_less_mult_iff linorder_not_less [symmetric])

lemma abs_mult: "abs (x * y) = abs x * abs (y::int)"
by (simp del: number_of_reorient split
          add: zabs_split split add: zabs_split add: zmult_less_0_iff zle_def)

lemma abs_eq_0 [iff]: "(abs x = 0) = (x = (0::int))"
by (simp split add: zabs_split)

lemma zero_less_abs_iff [iff]: "(0 < abs x) = (x ~= (0::int))"
by (simp split add: zabs_split, arith)

(* THIS LOOKS WRONG: [intro]*)
lemma square_nonzero [simp]: "0 \<le> x * (x::int)"
apply (subgoal_tac " (- x) * x \<le> 0")
 apply simp
apply (simp only: zmult_le_0_iff, auto)
done


subsection{*Products and 1, by T. M. Rasmussen*}

lemma zmult_eq_self_iff: "(m = m*(n::int)) = (n = 1 | m = 0)"
apply auto
apply (subgoal_tac "m*1 = m*n")
apply (drule zmult_cancel1 [THEN iffD1], auto)
done

lemma zless_1_zmult: "[| 1 < m; 1 < n |] ==> 1 < m*(n::int)"
apply (rule_tac y = "1*n" in order_less_trans)
apply (rule_tac [2] zmult_zless_mono1)
apply (simp_all (no_asm_simp))
done

lemma pos_zmult_eq_1_iff: "0 < (m::int) ==> (m * n = 1) = (m = 1 & n = 1)"
apply auto
apply (case_tac "m=1")
apply (case_tac [2] "n=1")
apply (case_tac [4] "m=1")
apply (case_tac [5] "n=1", auto)
apply (tactic"distinct_subgoals_tac")
apply (subgoal_tac "1<m*n", simp)
apply (rule zless_1_zmult, arith)
apply (subgoal_tac "0<n", arith)
apply (subgoal_tac "0<m*n")
apply (drule int_0_less_mult_iff [THEN iffD1], auto)
done

lemma zmult_eq_1_iff: "(m*n = (1::int)) = ((m = 1 & n = 1) | (m = -1 & n = -1))"
apply (case_tac "0<m")
apply (simp (no_asm_simp) add: pos_zmult_eq_1_iff)
apply (case_tac "m=0")
apply (simp (no_asm_simp) del: number_of_reorient)
apply (subgoal_tac "0 < -m")
apply (drule_tac n = "-n" in pos_zmult_eq_1_iff, auto)
done


subsection{*More about nat*}

lemma nat_add_distrib:
     "[| (0::int) \<le> z;  0 \<le> z' |] ==> nat (z+z') = nat z + nat z'"
apply (rule inj_int [THEN injD])
apply (simp (no_asm_simp) add: zadd_int [symmetric])
done

lemma nat_diff_distrib:
     "[| (0::int) \<le> z';  z' \<le> z |] ==> nat (z-z') = nat z - nat z'"
apply (rule inj_int [THEN injD])
apply (simp (no_asm_simp) add: zdiff_int [symmetric] nat_le_eq_zle)
done

lemma nat_mult_distrib: "(0::int) \<le> z ==> nat (z*z') = nat z * nat z'"
apply (case_tac "0 \<le> z'")
apply (rule inj_int [THEN injD])
apply (simp (no_asm_simp) add: zmult_int [symmetric] int_0_le_mult_iff)
apply (simp add: zmult_le_0_iff)
done

lemma nat_mult_distrib_neg: "z \<le> (0::int) ==> nat(z*z') = nat(-z) * nat(-z')"
apply (rule trans)
apply (rule_tac [2] nat_mult_distrib, auto)
done

lemma nat_abs_mult_distrib: "nat (abs (w * z)) = nat (abs w) * nat (abs z)"
apply (case_tac "z=0 | w=0")
apply (auto simp add: zabs_def nat_mult_distrib [symmetric] 
                      nat_mult_distrib_neg [symmetric] zmult_less_0_iff)
done

ML
{*
val zle_diff1_eq = thm "zle_diff1_eq";
val zle_add1_eq_le = thm "zle_add1_eq_le";
val nonneg_eq_int = thm "nonneg_eq_int";
val nat_eq_iff = thm "nat_eq_iff";
val nat_eq_iff2 = thm "nat_eq_iff2";
val nat_less_iff = thm "nat_less_iff";
val int_eq_iff = thm "int_eq_iff";
val nat_0 = thm "nat_0";
val nat_1 = thm "nat_1";
val nat_2 = thm "nat_2";
val nat_less_eq_zless = thm "nat_less_eq_zless";
val nat_le_eq_zle = thm "nat_le_eq_zle";
val zabs_split = thm "zabs_split";
val zero_le_zabs = thm "zero_le_zabs";

val int_diff_minus_eq = thm "int_diff_minus_eq";
val abs_abs = thm "abs_abs";
val abs_minus = thm "abs_minus";
val triangle_ineq = thm "triangle_ineq";
val nat_intermed_int_val = thm "nat_intermed_int_val";
val zmult_pos = thm "zmult_pos";
val zmult_neg = thm "zmult_neg";
val zmult_pos_neg = thm "zmult_pos_neg";
val int_0_less_mult_iff = thm "int_0_less_mult_iff";
val int_0_le_mult_iff = thm "int_0_le_mult_iff";
val zmult_less_0_iff = thm "zmult_less_0_iff";
val zmult_le_0_iff = thm "zmult_le_0_iff";
val abs_mult = thm "abs_mult";
val abs_eq_0 = thm "abs_eq_0";
val zero_less_abs_iff = thm "zero_less_abs_iff";
val square_nonzero = thm "square_nonzero";
val zmult_eq_self_iff = thm "zmult_eq_self_iff";
val zless_1_zmult = thm "zless_1_zmult";
val pos_zmult_eq_1_iff = thm "pos_zmult_eq_1_iff";
val zmult_eq_1_iff = thm "zmult_eq_1_iff";
val nat_add_distrib = thm "nat_add_distrib";
val nat_diff_distrib = thm "nat_diff_distrib";
val nat_mult_distrib = thm "nat_mult_distrib";
val nat_mult_distrib_neg = thm "nat_mult_distrib_neg";
val nat_abs_mult_distrib = thm "nat_abs_mult_distrib";
*}

end
