(*  Title:      HOL/Library/Fraction_Field.thy
    Author:     Amine Chaieb, University of Cambridge
*)

header{* A formalization of the fraction field of any integral domain;
         generalization of theory Rat from int to any integral domain *}

theory Fraction_Field
imports Main
begin

subsection {* General fractions construction *}

subsubsection {* Construction of the type of fractions *}

definition fractrel :: "(('a::idom * 'a ) * ('a * 'a)) set" where
  "fractrel = {(x, y). snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x}"

lemma fractrel_iff [simp]:
  "(x, y) \<in> fractrel \<longleftrightarrow> snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x"
  by (simp add: fractrel_def)

lemma refl_fractrel: "refl_on {x. snd x \<noteq> 0} fractrel"
  by (auto simp add: refl_on_def fractrel_def)

lemma sym_fractrel: "sym fractrel"
  by (simp add: fractrel_def sym_def)

lemma trans_fractrel: "trans fractrel"
proof (rule transI, unfold split_paired_all)
  fix a b a' b' a'' b'' :: 'a
  assume A: "((a, b), (a', b')) \<in> fractrel"
  assume B: "((a', b'), (a'', b'')) \<in> fractrel"
  have "b' * (a * b'') = b'' * (a * b')" by (simp add: mult_ac)
  also from A have "a * b' = a' * b" by auto
  also have "b'' * (a' * b) = b * (a' * b'')" by (simp add: mult_ac)
  also from B have "a' * b'' = a'' * b'" by auto
  also have "b * (a'' * b') = b' * (a'' * b)" by (simp add: mult_ac)
  finally have "b' * (a * b'') = b' * (a'' * b)" .
  moreover from B have "b' \<noteq> 0" by auto
  ultimately have "a * b'' = a'' * b" by simp
  with A B show "((a, b), (a'', b'')) \<in> fractrel" by auto
qed
  
lemma equiv_fractrel: "equiv {x. snd x \<noteq> 0} fractrel"
  by (rule equivI [OF refl_fractrel sym_fractrel trans_fractrel])

lemmas UN_fractrel = UN_equiv_class [OF equiv_fractrel]
lemmas UN_fractrel2 = UN_equiv_class2 [OF equiv_fractrel equiv_fractrel]

lemma equiv_fractrel_iff [iff]: 
  assumes "snd x \<noteq> 0" and "snd y \<noteq> 0"
  shows "fractrel `` {x} = fractrel `` {y} \<longleftrightarrow> (x, y) \<in> fractrel"
  by (rule eq_equiv_class_iff, rule equiv_fractrel) (auto simp add: assms)

definition "fract = {(x::'a\<times>'a). snd x \<noteq> (0::'a::idom)} // fractrel"

typedef (open) 'a fract = "fract :: ('a * 'a::idom) set set"
  unfolding fract_def
proof
  have "(0::'a, 1::'a) \<in> {x. snd x \<noteq> 0}" by simp
  then show "fractrel `` {(0::'a, 1)} \<in> {x. snd x \<noteq> 0} // fractrel" by (rule quotientI)
qed

lemma fractrel_in_fract [simp]: "snd x \<noteq> 0 \<Longrightarrow> fractrel `` {x} \<in> fract"
  by (simp add: fract_def quotientI)

declare Abs_fract_inject [simp] Abs_fract_inverse [simp]


subsubsection {* Representation and basic operations *}

definition Fract :: "'a::idom \<Rightarrow> 'a \<Rightarrow> 'a fract" where
  "Fract a b = Abs_fract (fractrel `` {if b = 0 then (0, 1) else (a, b)})"

code_datatype Fract

lemma Fract_cases [case_names Fract, cases type: fract]:
  assumes "\<And>a b. q = Fract a b \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> C"
  shows C
  using assms by (cases q) (clarsimp simp add: Fract_def fract_def quotient_def)

lemma Fract_induct [case_names Fract, induct type: fract]:
  assumes "\<And>a b. b \<noteq> 0 \<Longrightarrow> P (Fract a b)"
  shows "P q"
  using assms by (cases q) simp

lemma eq_fract:
  shows "\<And>a b c d. b \<noteq> 0 \<Longrightarrow> d \<noteq> 0 \<Longrightarrow> Fract a b = Fract c d \<longleftrightarrow> a * d = c * b"
  and "\<And>a. Fract a 0 = Fract 0 1"
  and "\<And>a c. Fract 0 a = Fract 0 c"
  by (simp_all add: Fract_def)

instantiation fract :: (idom) "{comm_ring_1, power}"
begin

definition Zero_fract_def [code_unfold]: "0 = Fract 0 1"

definition One_fract_def [code_unfold]: "1 = Fract 1 1"

definition add_fract_def:
  "q + r = Abs_fract (\<Union>x \<in> Rep_fract q. \<Union>y \<in> Rep_fract r.
    fractrel `` {(fst x * snd y + fst y * snd x, snd x * snd y)})"

lemma add_fract [simp]:
  assumes "b \<noteq> (0::'a::idom)" and "d \<noteq> 0"
  shows "Fract a b + Fract c d = Fract (a * d + c * b) (b * d)"
proof -
  have "(\<lambda>x y. fractrel``{(fst x * snd y + fst y * snd x, snd x * snd y :: 'a)})
    respects2 fractrel"
  apply (rule equiv_fractrel [THEN congruent2_commuteI]) apply (auto simp add: algebra_simps)
  unfolding mult_assoc[symmetric] .
  with assms show ?thesis by (simp add: Fract_def add_fract_def UN_fractrel2)
qed

definition minus_fract_def:
  "- q = Abs_fract (\<Union>x \<in> Rep_fract q. fractrel `` {(- fst x, snd x)})"

lemma minus_fract [simp, code]: "- Fract a b = Fract (- a) (b::'a::idom)"
proof -
  have "(\<lambda>x. fractrel `` {(- fst x, snd x :: 'a)}) respects fractrel"
    by (simp add: congruent_def split_paired_all)
  then show ?thesis by (simp add: Fract_def minus_fract_def UN_fractrel)
qed

lemma minus_fract_cancel [simp]: "Fract (- a) (- b) = Fract a b"
  by (cases "b = 0") (simp_all add: eq_fract)

definition diff_fract_def: "q - r = q + - (r::'a fract)"

lemma diff_fract [simp]:
  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "Fract a b - Fract c d = Fract (a * d - c * b) (b * d)"
  using assms by (simp add: diff_fract_def diff_minus)

definition mult_fract_def:
  "q * r = Abs_fract (\<Union>x \<in> Rep_fract q. \<Union>y \<in> Rep_fract r.
    fractrel``{(fst x * fst y, snd x * snd y)})"

lemma mult_fract [simp]: "Fract (a::'a::idom) b * Fract c d = Fract (a * c) (b * d)"
proof -
  have "(\<lambda>x y. fractrel `` {(fst x * fst y, snd x * snd y :: 'a)}) respects2 fractrel"
    apply (rule equiv_fractrel [THEN congruent2_commuteI]) apply (auto simp add: algebra_simps)
    unfolding mult_assoc[symmetric] .
  then show ?thesis by (simp add: Fract_def mult_fract_def UN_fractrel2)
qed

lemma mult_fract_cancel:
  assumes "c \<noteq> (0::'a)"
  shows "Fract (c * a) (c * b) = Fract a b"
proof -
  from assms have "Fract c c = Fract 1 1" by (simp add: Fract_def)
  then show ?thesis by (simp add: mult_fract [symmetric])
qed

instance
proof
  fix q r s :: "'a fract" show "(q * r) * s = q * (r * s)" 
    by (cases q, cases r, cases s) (simp add: eq_fract algebra_simps)
next
  fix q r :: "'a fract" show "q * r = r * q"
    by (cases q, cases r) (simp add: eq_fract algebra_simps)
next
  fix q :: "'a fract" show "1 * q = q"
    by (cases q) (simp add: One_fract_def eq_fract)
next
  fix q r s :: "'a fract" show "(q + r) + s = q + (r + s)"
    by (cases q, cases r, cases s) (simp add: eq_fract algebra_simps)
next
  fix q r :: "'a fract" show "q + r = r + q"
    by (cases q, cases r) (simp add: eq_fract algebra_simps)
next
  fix q :: "'a fract" show "0 + q = q"
    by (cases q) (simp add: Zero_fract_def eq_fract)
next
  fix q :: "'a fract" show "- q + q = 0"
    by (cases q) (simp add: Zero_fract_def eq_fract)
next
  fix q r :: "'a fract" show "q - r = q + - r"
    by (cases q, cases r) (simp add: eq_fract)
next
  fix q r s :: "'a fract" show "(q + r) * s = q * s + r * s"
    by (cases q, cases r, cases s) (simp add: eq_fract algebra_simps)
next
  show "(0::'a fract) \<noteq> 1" by (simp add: Zero_fract_def One_fract_def eq_fract)
qed

end

lemma of_nat_fract: "of_nat k = Fract (of_nat k) 1"
  by (induct k) (simp_all add: Zero_fract_def One_fract_def)

lemma Fract_of_nat_eq: "Fract (of_nat k) 1 = of_nat k"
  by (rule of_nat_fract [symmetric])

lemma fract_collapse [code_post]:
  "Fract 0 k = 0"
  "Fract 1 1 = 1"
  "Fract k 0 = 0"
  by (cases "k = 0")
    (simp_all add: Zero_fract_def One_fract_def eq_fract Fract_def)

lemma fract_expand [code_unfold]:
  "0 = Fract 0 1"
  "1 = Fract 1 1"
  by (simp_all add: fract_collapse)

lemma Fract_cases_nonzero [case_names Fract 0]:
  assumes Fract: "\<And>a b. q = Fract a b \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> C"
  assumes 0: "q = 0 \<Longrightarrow> C"
  shows C
proof (cases "q = 0")
  case True then show C using 0 by auto
next
  case False
  then obtain a b where "q = Fract a b" and "b \<noteq> 0" by (cases q) auto
  moreover with False have "0 \<noteq> Fract a b" by simp
  with `b \<noteq> 0` have "a \<noteq> 0" by (simp add: Zero_fract_def eq_fract)
  with Fract `q = Fract a b` `b \<noteq> 0` show C by auto
qed
  


subsubsection {* The field of rational numbers *}

context idom
begin
subclass ring_no_zero_divisors ..
thm mult_eq_0_iff
end

instantiation fract :: (idom) field_inverse_zero
begin

definition inverse_fract_def:
  "inverse q = Abs_fract (\<Union>x \<in> Rep_fract q.
     fractrel `` {if fst x = 0 then (0, 1) else (snd x, fst x)})"


lemma inverse_fract [simp]: "inverse (Fract a b) = Fract (b::'a::idom) a"
proof -
  have stupid: "\<And>x. (0::'a) = x \<longleftrightarrow> x = 0" by auto
  have "(\<lambda>x. fractrel `` {if fst x = 0 then (0, 1) else (snd x, fst x :: 'a)}) respects fractrel"
    by (auto simp add: congruent_def stupid algebra_simps)
  then show ?thesis by (simp add: Fract_def inverse_fract_def UN_fractrel)
qed

definition divide_fract_def: "q / r = q * inverse (r:: 'a fract)"

lemma divide_fract [simp]: "Fract a b / Fract c d = Fract (a * d) (b * c)"
  by (simp add: divide_fract_def)

instance
proof
  fix q :: "'a fract"
  assume "q \<noteq> 0"
  then show "inverse q * q = 1"
    by (cases q rule: Fract_cases_nonzero)
      (simp_all add: fract_expand eq_fract mult_commute)
next
  fix q r :: "'a fract"
  show "q / r = q * inverse r" by (simp add: divide_fract_def)
next
  show "inverse 0 = (0:: 'a fract)"
    by (simp add: fract_expand) (simp add: fract_collapse)
qed

end


subsubsection {* The ordered field of fractions over an ordered idom *}

lemma le_congruent2:
  "(\<lambda>x y::'a \<times> 'a::linordered_idom.
    {(fst x * snd y)*(snd x * snd y) \<le> (fst y * snd x)*(snd x * snd y)})
    respects2 fractrel"
proof (clarsimp simp add: congruent2_def)
  fix a b a' b' c d c' d' :: 'a
  assume neq: "b \<noteq> 0"  "b' \<noteq> 0"  "d \<noteq> 0"  "d' \<noteq> 0"
  assume eq1: "a * b' = a' * b"
  assume eq2: "c * d' = c' * d"

  let ?le = "\<lambda>a b c d. ((a * d) * (b * d) \<le> (c * b) * (b * d))"
  {
    fix a b c d x :: 'a assume x: "x \<noteq> 0"
    have "?le a b c d = ?le (a * x) (b * x) c d"
    proof -
      from x have "0 < x * x" by (auto simp add: zero_less_mult_iff)
      then have "?le a b c d =
          ((a * d) * (b * d) * (x * x) \<le> (c * b) * (b * d) * (x * x))"
        by (simp add: mult_le_cancel_right)
      also have "... = ?le (a * x) (b * x) c d"
        by (simp add: mult_ac)
      finally show ?thesis .
    qed
  } note le_factor = this

  let ?D = "b * d" and ?D' = "b' * d'"
  from neq have D: "?D \<noteq> 0" by simp
  from neq have "?D' \<noteq> 0" by simp
  then have "?le a b c d = ?le (a * ?D') (b * ?D') c d"
    by (rule le_factor)
  also have "... = ((a * b') * ?D * ?D' * d * d' \<le> (c * d') * ?D * ?D' * b * b')"
    by (simp add: mult_ac)
  also have "... = ((a' * b) * ?D * ?D' * d * d' \<le> (c' * d) * ?D * ?D' * b * b')"
    by (simp only: eq1 eq2)
  also have "... = ?le (a' * ?D) (b' * ?D) c' d'"
    by (simp add: mult_ac)
  also from D have "... = ?le a' b' c' d'"
    by (rule le_factor [symmetric])
  finally show "?le a b c d = ?le a' b' c' d'" .
qed

instantiation fract :: (linordered_idom) linorder
begin

definition le_fract_def:
   "q \<le> r \<longleftrightarrow> the_elem (\<Union>x \<in> Rep_fract q. \<Union>y \<in> Rep_fract r.
      {(fst x * snd y)*(snd x * snd y) \<le> (fst y * snd x)*(snd x * snd y)})"

definition less_fract_def: "z < (w::'a fract) \<longleftrightarrow> z \<le> w \<and> \<not> w \<le> z"

lemma le_fract [simp]:
  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "Fract a b \<le> Fract c d \<longleftrightarrow> (a * d) * (b * d) \<le> (c * b) * (b * d)"
by (simp add: Fract_def le_fract_def le_congruent2 UN_fractrel2 assms)

lemma less_fract [simp]:
  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "Fract a b < Fract c d \<longleftrightarrow> (a * d) * (b * d) < (c * b) * (b * d)"
by (simp add: less_fract_def less_le_not_le mult_ac assms)

instance
proof
  fix q r s :: "'a fract"
  assume "q \<le> r" and "r \<le> s" thus "q \<le> s"
  proof (induct q, induct r, induct s)
    fix a b c d e f :: 'a
    assume neq: "b \<noteq> 0"  "d \<noteq> 0"  "f \<noteq> 0"
    assume 1: "Fract a b \<le> Fract c d" and 2: "Fract c d \<le> Fract e f"
    show "Fract a b \<le> Fract e f"
    proof -
      from neq obtain bb: "0 < b * b" and dd: "0 < d * d" and ff: "0 < f * f"
        by (auto simp add: zero_less_mult_iff linorder_neq_iff)
      have "(a * d) * (b * d) * (f * f) \<le> (c * b) * (b * d) * (f * f)"
      proof -
        from neq 1 have "(a * d) * (b * d) \<le> (c * b) * (b * d)"
          by simp
        with ff show ?thesis by (simp add: mult_le_cancel_right)
      qed
      also have "... = (c * f) * (d * f) * (b * b)"
        by (simp only: mult_ac)
      also have "... \<le> (e * d) * (d * f) * (b * b)"
      proof -
        from neq 2 have "(c * f) * (d * f) \<le> (e * d) * (d * f)"
          by simp
        with bb show ?thesis by (simp add: mult_le_cancel_right)
      qed
      finally have "(a * f) * (b * f) * (d * d) \<le> e * b * (b * f) * (d * d)"
        by (simp only: mult_ac)
      with dd have "(a * f) * (b * f) \<le> (e * b) * (b * f)"
        by (simp add: mult_le_cancel_right)
      with neq show ?thesis by simp
    qed
  qed
next
  fix q r :: "'a fract"
  assume "q \<le> r" and "r \<le> q" thus "q = r"
  proof (induct q, induct r)
    fix a b c d :: 'a
    assume neq: "b \<noteq> 0"  "d \<noteq> 0"
    assume 1: "Fract a b \<le> Fract c d" and 2: "Fract c d \<le> Fract a b"
    show "Fract a b = Fract c d"
    proof -
      from neq 1 have "(a * d) * (b * d) \<le> (c * b) * (b * d)"
        by simp
      also have "... \<le> (a * d) * (b * d)"
      proof -
        from neq 2 have "(c * b) * (d * b) \<le> (a * d) * (d * b)"
          by simp
        thus ?thesis by (simp only: mult_ac)
      qed
      finally have "(a * d) * (b * d) = (c * b) * (b * d)" .
      moreover from neq have "b * d \<noteq> 0" by simp
      ultimately have "a * d = c * b" by simp
      with neq show ?thesis by (simp add: eq_fract)
    qed
  qed
next
  fix q r :: "'a fract"
  show "q \<le> q"
    by (induct q) simp
  show "(q < r) = (q \<le> r \<and> \<not> r \<le> q)"
    by (simp only: less_fract_def)
  show "q \<le> r \<or> r \<le> q"
    by (induct q, induct r)
       (simp add: mult_commute, rule linorder_linear)
qed

end

instantiation fract :: (linordered_idom) "{distrib_lattice, abs_if, sgn_if}"
begin

definition abs_fract_def: "\<bar>q\<bar> = (if q < 0 then -q else (q::'a fract))"

definition sgn_fract_def:
  "sgn (q::'a fract) = (if q=0 then 0 else if 0<q then 1 else - 1)"

theorem abs_fract [simp]: "\<bar>Fract a b\<bar> = Fract \<bar>a\<bar> \<bar>b\<bar>"
  by (auto simp add: abs_fract_def Zero_fract_def le_less
      eq_fract zero_less_mult_iff mult_less_0_iff split: abs_split)

definition inf_fract_def:
  "(inf \<Colon> 'a fract \<Rightarrow> 'a fract \<Rightarrow> 'a fract) = min"

definition sup_fract_def:
  "(sup \<Colon> 'a fract \<Rightarrow> 'a fract \<Rightarrow> 'a fract) = max"

instance
  by intro_classes
    (auto simp add: abs_fract_def sgn_fract_def
      min_max.sup_inf_distrib1 inf_fract_def sup_fract_def)

end

instance fract :: (linordered_idom) linordered_field_inverse_zero
proof
  fix q r s :: "'a fract"
  show "q \<le> r ==> s + q \<le> s + r"
  proof (induct q, induct r, induct s)
    fix a b c d e f :: 'a
    assume neq: "b \<noteq> 0"  "d \<noteq> 0"  "f \<noteq> 0"
    assume le: "Fract a b \<le> Fract c d"
    show "Fract e f + Fract a b \<le> Fract e f + Fract c d"
    proof -
      let ?F = "f * f" from neq have F: "0 < ?F"
        by (auto simp add: zero_less_mult_iff)
      from neq le have "(a * d) * (b * d) \<le> (c * b) * (b * d)"
        by simp
      with F have "(a * d) * (b * d) * ?F * ?F \<le> (c * b) * (b * d) * ?F * ?F"
        by (simp add: mult_le_cancel_right)
      with neq show ?thesis by (simp add: field_simps)
    qed
  qed
  show "q < r ==> 0 < s ==> s * q < s * r"
  proof (induct q, induct r, induct s)
    fix a b c d e f :: 'a
    assume neq: "b \<noteq> 0"  "d \<noteq> 0"  "f \<noteq> 0"
    assume le: "Fract a b < Fract c d"
    assume gt: "0 < Fract e f"
    show "Fract e f * Fract a b < Fract e f * Fract c d"
    proof -
      let ?E = "e * f" and ?F = "f * f"
      from neq gt have "0 < ?E"
        by (auto simp add: Zero_fract_def order_less_le eq_fract)
      moreover from neq have "0 < ?F"
        by (auto simp add: zero_less_mult_iff)
      moreover from neq le have "(a * d) * (b * d) < (c * b) * (b * d)"
        by simp
      ultimately have "(a * d) * (b * d) * ?E * ?F < (c * b) * (b * d) * ?E * ?F"
        by (simp add: mult_less_cancel_right)
      with neq show ?thesis
        by (simp add: mult_ac)
    qed
  qed
qed

lemma fract_induct_pos [case_names Fract]:
  fixes P :: "'a::linordered_idom fract \<Rightarrow> bool"
  assumes step: "\<And>a b. 0 < b \<Longrightarrow> P (Fract a b)"
  shows "P q"
proof (cases q)
  have step': "\<And>a b. b < 0 \<Longrightarrow> P (Fract a b)"
  proof -
    fix a::'a and b::'a
    assume b: "b < 0"
    then have "0 < -b" by simp
    then have "P (Fract (-a) (-b))" by (rule step)
    thus "P (Fract a b)" by (simp add: order_less_imp_not_eq [OF b])
  qed
  case (Fract a b)
  thus "P q" by (force simp add: linorder_neq_iff step step')
qed

lemma zero_less_Fract_iff:
  "0 < b \<Longrightarrow> 0 < Fract a b \<longleftrightarrow> 0 < a"
  by (auto simp add: Zero_fract_def zero_less_mult_iff)

lemma Fract_less_zero_iff:
  "0 < b \<Longrightarrow> Fract a b < 0 \<longleftrightarrow> a < 0"
  by (auto simp add: Zero_fract_def mult_less_0_iff)

lemma zero_le_Fract_iff:
  "0 < b \<Longrightarrow> 0 \<le> Fract a b \<longleftrightarrow> 0 \<le> a"
  by (auto simp add: Zero_fract_def zero_le_mult_iff)

lemma Fract_le_zero_iff:
  "0 < b \<Longrightarrow> Fract a b \<le> 0 \<longleftrightarrow> a \<le> 0"
  by (auto simp add: Zero_fract_def mult_le_0_iff)

lemma one_less_Fract_iff:
  "0 < b \<Longrightarrow> 1 < Fract a b \<longleftrightarrow> b < a"
  by (auto simp add: One_fract_def mult_less_cancel_right_disj)

lemma Fract_less_one_iff:
  "0 < b \<Longrightarrow> Fract a b < 1 \<longleftrightarrow> a < b"
  by (auto simp add: One_fract_def mult_less_cancel_right_disj)

lemma one_le_Fract_iff:
  "0 < b \<Longrightarrow> 1 \<le> Fract a b \<longleftrightarrow> b \<le> a"
  by (auto simp add: One_fract_def mult_le_cancel_right)

lemma Fract_le_one_iff:
  "0 < b \<Longrightarrow> Fract a b \<le> 1 \<longleftrightarrow> a \<le> b"
  by (auto simp add: One_fract_def mult_le_cancel_right)

end
