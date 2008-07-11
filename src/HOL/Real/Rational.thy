(*  Title:  HOL/Library/Rational.thy
    ID:     $Id$
    Author: Markus Wenzel, TU Muenchen
*)

header {* Rational numbers *}

theory Rational
imports "../Presburger" GCD Abstract_Rat
uses ("rat_arith.ML")
begin

subsection {* Rational numbers as quotient *}

subsubsection {* Construction of the type of rational numbers *}

definition
  ratrel :: "((int \<times> int) \<times> (int \<times> int)) set" where
  "ratrel = {(x, y). snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x}"

lemma ratrel_iff [simp]:
  "(x, y) \<in> ratrel \<longleftrightarrow> snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x"
  by (simp add: ratrel_def)

lemma refl_ratrel: "refl {x. snd x \<noteq> 0} ratrel"
  by (auto simp add: refl_def ratrel_def)

lemma sym_ratrel: "sym ratrel"
  by (simp add: ratrel_def sym_def)

lemma trans_ratrel: "trans ratrel"
proof (rule transI, unfold split_paired_all)
  fix a b a' b' a'' b'' :: int
  assume A: "((a, b), (a', b')) \<in> ratrel"
  assume B: "((a', b'), (a'', b'')) \<in> ratrel"
  have "b' * (a * b'') = b'' * (a * b')" by simp
  also from A have "a * b' = a' * b" by auto
  also have "b'' * (a' * b) = b * (a' * b'')" by simp
  also from B have "a' * b'' = a'' * b'" by auto
  also have "b * (a'' * b') = b' * (a'' * b)" by simp
  finally have "b' * (a * b'') = b' * (a'' * b)" .
  moreover from B have "b' \<noteq> 0" by auto
  ultimately have "a * b'' = a'' * b" by simp
  with A B show "((a, b), (a'', b'')) \<in> ratrel" by auto
qed
  
lemma equiv_ratrel: "equiv {x. snd x \<noteq> 0} ratrel"
  by (rule equiv.intro [OF refl_ratrel sym_ratrel trans_ratrel])

lemmas UN_ratrel = UN_equiv_class [OF equiv_ratrel]
lemmas UN_ratrel2 = UN_equiv_class2 [OF equiv_ratrel equiv_ratrel]

lemma equiv_ratrel_iff [iff]: 
  assumes "snd x \<noteq> 0" and "snd y \<noteq> 0"
  shows "ratrel `` {x} = ratrel `` {y} \<longleftrightarrow> (x, y) \<in> ratrel"
  by (rule eq_equiv_class_iff, rule equiv_ratrel) (auto simp add: assms)

typedef (Rat) rat = "{x. snd x \<noteq> 0} // ratrel"
proof
  have "(0::int, 1::int) \<in> {x. snd x \<noteq> 0}" by simp
  then show "ratrel `` {(0, 1)} \<in> {x. snd x \<noteq> 0} // ratrel" by (rule quotientI)
qed

lemma ratrel_in_Rat [simp]: "snd x \<noteq> 0 \<Longrightarrow> ratrel `` {x} \<in> Rat"
  by (simp add: Rat_def quotientI)

declare Abs_Rat_inject [simp] Abs_Rat_inverse [simp]


subsubsection {* Representation and basic operations *}

definition
  Fract :: "int \<Rightarrow> int \<Rightarrow> rat" where
  [code func del]: "Fract a b = Abs_Rat (ratrel `` {if b = 0 then (0, 1) else (a, b)})"

code_datatype Fract

lemma Rat_cases [case_names Fract, cases type: rat]:
  assumes "\<And>a b. q = Fract a b \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> C"
  shows C
  using assms by (cases q) (clarsimp simp add: Fract_def Rat_def quotient_def)

lemma Rat_induct [case_names Fract, induct type: rat]:
  assumes "\<And>a b. b \<noteq> 0 \<Longrightarrow> P (Fract a b)"
  shows "P q"
  using assms by (cases q) simp

lemma eq_rat:
  shows "\<And>a b c d. b \<noteq> 0 \<Longrightarrow> d \<noteq> 0 \<Longrightarrow> Fract a b = Fract c d \<longleftrightarrow> a * d = c * b"
  and "\<And>a c. Fract a 0 = Fract c 0"
  by (simp_all add: Fract_def)

instantiation rat :: "{comm_ring_1, recpower}"
begin

definition
  Zero_rat_def [code, code unfold]: "0 = Fract 0 1"

definition
  One_rat_def [code, code unfold]: "1 = Fract 1 1"

definition
  add_rat_def [code func del]:
  "q + r = Abs_Rat (\<Union>x \<in> Rep_Rat q. \<Union>y \<in> Rep_Rat r.
    ratrel `` {(fst x * snd y + fst y * snd x, snd x * snd y)})"

lemma add_rat:
  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "Fract a b + Fract c d = Fract (a * d + c * b) (b * d)"
proof -
  have "(\<lambda>x y. ratrel``{(fst x * snd y + fst y * snd x, snd x * snd y)})
    respects2 ratrel"
  by (rule equiv_ratrel [THEN congruent2_commuteI]) (simp_all add: left_distrib)
  with assms show ?thesis by (simp add: Fract_def add_rat_def UN_ratrel2)
qed

definition
  minus_rat_def [code func del]:
  "- q = Abs_Rat (\<Union>x \<in> Rep_Rat q. ratrel `` {(- fst x, snd x)})"

lemma minus_rat: "- Fract a b = Fract (- a) b"
proof -
  have "(\<lambda>x. ratrel `` {(- fst x, snd x)}) respects ratrel"
    by (simp add: congruent_def)
  then show ?thesis by (simp add: Fract_def minus_rat_def UN_ratrel)
qed

lemma minus_rat_cancel [simp]: 
  "Fract (- a) (- b) = Fract a b"
  by (cases "b = 0") (simp_all add: eq_rat)

definition
  diff_rat_def [code func del]: "q - r = q + - (r::rat)"

lemma diff_rat:
  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "Fract a b - Fract c d = Fract (a * d - c * b) (b * d)"
  using assms by (simp add: diff_rat_def add_rat minus_rat)

definition
  mult_rat_def [code func del]:
  "q * r = Abs_Rat (\<Union>x \<in> Rep_Rat q. \<Union>y \<in> Rep_Rat r.
    ratrel``{(fst x * fst y, snd x * snd y)})"

lemma mult_rat: "Fract a b * Fract c d = Fract (a * c) (b * d)"
proof -
  have "(\<lambda>x y. ratrel `` {(fst x * fst y, snd x * snd y)}) respects2 ratrel"
    by (rule equiv_ratrel [THEN congruent2_commuteI]) simp_all
  then show ?thesis by (simp add: Fract_def mult_rat_def UN_ratrel2)
qed

lemma mult_rat_cancel [simp]:
  assumes "c \<noteq> 0"
  shows "Fract (c * a) (c * b) = Fract a b"
proof -
  from assms have "Fract c c = Fract 1 1" by (simp add: Fract_def)
  then show ?thesis by (simp add: mult_rat [symmetric] mult_rat)
qed

primrec power_rat
where
  rat_power_0:     "q ^ 0 = (1\<Colon>rat)"
  | rat_power_Suc: "q ^ Suc n = (q\<Colon>rat) * (q ^ n)"

instance proof
  fix q r s :: rat show "(q * r) * s = q * (r * s)"
    by (cases q, cases r, cases s) (simp add: mult_rat eq_rat)
next
  fix q r :: rat show "q * r = r * q"
    by (cases q, cases r) (simp add: mult_rat eq_rat)
next
  fix q :: rat show "1 * q = q"
    by (cases q) (simp add: One_rat_def mult_rat eq_rat)
next
  fix q r s :: rat show "(q + r) + s = q + (r + s)"
    by (cases q, cases r, cases s) (simp add: add_rat eq_rat ring_simps)
next
  fix q r :: rat show "q + r = r + q"
    by (cases q, cases r) (simp add: add_rat eq_rat)
next
  fix q :: rat show "0 + q = q"
    by (cases q) (simp add: Zero_rat_def add_rat eq_rat)
next
  fix q :: rat show "- q + q = 0"
    by (cases q) (simp add: Zero_rat_def add_rat minus_rat eq_rat)
next
  fix q r :: rat show "q - r = q + - r"
    by (cases q, cases r) (simp add: diff_rat add_rat minus_rat eq_rat)
next
  fix q r s :: rat show "(q + r) * s = q * s + r * s"
    by (cases q, cases r, cases s) (simp add: add_rat mult_rat eq_rat ring_simps)
next
  show "(0::rat) \<noteq> 1" by (simp add: Zero_rat_def One_rat_def eq_rat)
next
  fix q :: rat show "q * 1 = q"
    by (cases q) (simp add: One_rat_def mult_rat eq_rat)
next
  fix q :: rat
  fix n :: nat
  show "q ^ 0 = 1" by simp
  show "q ^ (Suc n) = q * (q ^ n)" by simp
qed

end

lemma of_nat_rat: "of_nat k = Fract (of_nat k) 1"
  by (induct k) (simp_all add: Zero_rat_def One_rat_def add_rat)

lemma of_int_rat: "of_int k = Fract k 1"
  by (cases k rule: int_diff_cases, simp add: of_nat_rat diff_rat)

lemma Fract_of_nat_eq: "Fract (of_nat k) 1 = of_nat k"
  by (rule of_nat_rat [symmetric])

lemma Fract_of_int_eq: "Fract k 1 = of_int k"
  by (rule of_int_rat [symmetric])

instantiation rat :: number_ring
begin

definition
  rat_number_of_def [code func del]: "number_of w = Fract w 1"

instance by intro_classes (simp add: rat_number_of_def of_int_rat)

end

lemma rat_number_collapse [code post]:
  "Fract 0 k = 0"
  "Fract 1 1 = 1"
  "Fract (number_of k) 1 = number_of k"
  "Fract k 0 = 0"
  by (cases "k = 0")
    (simp_all add: Zero_rat_def One_rat_def number_of_is_id number_of_eq of_int_rat eq_rat Fract_def)

lemma rat_number_expand [code unfold]:
  "0 = Fract 0 1"
  "1 = Fract 1 1"
  "number_of k = Fract (number_of k) 1"
  by (simp_all add: rat_number_collapse)

lemma iszero_rat [simp]:
  "iszero (number_of k :: rat) \<longleftrightarrow> iszero (number_of k :: int)"
  by (simp add: iszero_def rat_number_expand number_of_is_id eq_rat)

lemma Rat_cases_nonzero [case_names Fract 0]:
  assumes Fract: "\<And>a b. q = Fract a b \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> C"
  assumes 0: "q = 0 \<Longrightarrow> C"
  shows C
proof (cases "q = 0")
  case True then show C using 0 by auto
next
  case False
  then obtain a b where "q = Fract a b" and "b \<noteq> 0" by (cases q) auto
  moreover with False have "0 \<noteq> Fract a b" by simp
  with `b \<noteq> 0` have "a \<noteq> 0" by (simp add: Zero_rat_def eq_rat)
  with Fract `q = Fract a b` `b \<noteq> 0` show C by auto
qed
  


subsubsection {* The field of rational numbers *}

instantiation rat :: "{field, division_by_zero}"
begin

definition
  inverse_rat_def [code func del]:
  "inverse q = Abs_Rat (\<Union>x \<in> Rep_Rat q.
     ratrel `` {if fst x = 0 then (0, 1) else (snd x, fst x)})"

lemma inverse_rat: "inverse (Fract a b) = Fract b a"
proof -
  have "(\<lambda>x. ratrel `` {if fst x = 0 then (0, 1) else (snd x, fst x)}) respects ratrel"
    by (auto simp add: congruent_def mult_commute)
  then show ?thesis by (simp add: Fract_def inverse_rat_def UN_ratrel)
qed

definition
  divide_rat_def [code func del]: "q / r = q * inverse (r::rat)"

lemma divide_rat: "Fract a b / Fract c d = Fract (a * d) (b * c)"
  by (simp add: divide_rat_def inverse_rat mult_rat)

instance proof
  show "inverse 0 = (0::rat)" by (simp add: rat_number_expand inverse_rat)
    (simp add: rat_number_collapse)
next
  fix q :: rat
  assume "q \<noteq> 0"
  then show "inverse q * q = 1" by (cases q rule: Rat_cases_nonzero)
   (simp_all add: mult_rat  inverse_rat rat_number_expand eq_rat)
next
  fix q r :: rat
  show "q / r = q * inverse r" by (simp add: divide_rat_def)
qed

end


subsubsection {* Various *}

lemma Fract_add_one: "n \<noteq> 0 ==> Fract (m + n) n = Fract m n + 1"
  by (simp add: rat_number_expand add_rat)

lemma Fract_of_int_quotient: "Fract k l = of_int k / of_int l"
  by (simp add: Fract_of_int_eq [symmetric] divide_rat)

lemma Fract_number_of_quotient [code post]:
  "Fract (number_of k) (number_of l) = number_of k / number_of l"
  unfolding Fract_of_int_quotient number_of_is_id number_of_eq ..


subsubsection {* The ordered field of rational numbers *}

instantiation rat :: linorder
begin

definition
  le_rat_def [code func del]:
   "q \<le> r \<longleftrightarrow> contents (\<Union>x \<in> Rep_Rat q. \<Union>y \<in> Rep_Rat r.
      {(fst x * snd y) * (snd x * snd y) \<le> (fst y * snd x) * (snd x * snd y)})"

lemma le_rat:
  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "Fract a b \<le> Fract c d \<longleftrightarrow> (a * d) * (b * d) \<le> (c * b) * (b * d)"
proof -
  have "(\<lambda>x y. {(fst x * snd y) * (snd x * snd y) \<le> (fst y * snd x) * (snd x * snd y)})
    respects2 ratrel"
  proof (clarsimp simp add: congruent2_def)
    fix a b a' b' c d c' d'::int
    assume neq: "b \<noteq> 0"  "b' \<noteq> 0"  "d \<noteq> 0"  "d' \<noteq> 0"
    assume eq1: "a * b' = a' * b"
    assume eq2: "c * d' = c' * d"

    let ?le = "\<lambda>a b c d. ((a * d) * (b * d) \<le> (c * b) * (b * d))"
    {
      fix a b c d x :: int assume x: "x \<noteq> 0"
      have "?le a b c d = ?le (a * x) (b * x) c d"
      proof -
        from x have "0 < x * x" by (auto simp add: zero_less_mult_iff)
        hence "?le a b c d =
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
    hence "?le a b c d = ?le (a * ?D') (b * ?D') c d"
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
  with assms show ?thesis by (simp add: Fract_def le_rat_def UN_ratrel2)
qed

definition
  less_rat_def [code func del]: "z < (w::rat) \<longleftrightarrow> z \<le> w \<and> z \<noteq> w"

lemma less_rat:
  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "Fract a b < Fract c d \<longleftrightarrow> (a * d) * (b * d) < (c * b) * (b * d)"
  using assms by (simp add: less_rat_def le_rat eq_rat order_less_le)

instance proof
  fix q r s :: rat
  {
    assume "q \<le> r" and "r \<le> s"
    show "q \<le> s"
    proof (insert prems, induct q, induct r, induct s)
      fix a b c d e f :: int
      assume neq: "b \<noteq> 0"  "d \<noteq> 0"  "f \<noteq> 0"
      assume 1: "Fract a b \<le> Fract c d" and 2: "Fract c d \<le> Fract e f"
      show "Fract a b \<le> Fract e f"
      proof -
        from neq obtain bb: "0 < b * b" and dd: "0 < d * d" and ff: "0 < f * f"
          by (auto simp add: zero_less_mult_iff linorder_neq_iff)
        have "(a * d) * (b * d) * (f * f) \<le> (c * b) * (b * d) * (f * f)"
        proof -
          from neq 1 have "(a * d) * (b * d) \<le> (c * b) * (b * d)"
            by (simp add: le_rat)
          with ff show ?thesis by (simp add: mult_le_cancel_right)
        qed
        also have "... = (c * f) * (d * f) * (b * b)"
          by (simp only: mult_ac)
        also have "... \<le> (e * d) * (d * f) * (b * b)"
        proof -
          from neq 2 have "(c * f) * (d * f) \<le> (e * d) * (d * f)"
            by (simp add: le_rat)
          with bb show ?thesis by (simp add: mult_le_cancel_right)
        qed
        finally have "(a * f) * (b * f) * (d * d) \<le> e * b * (b * f) * (d * d)"
          by (simp only: mult_ac)
        with dd have "(a * f) * (b * f) \<le> (e * b) * (b * f)"
          by (simp add: mult_le_cancel_right)
        with neq show ?thesis by (simp add: le_rat)
      qed
    qed
  next
    assume "q \<le> r" and "r \<le> q"
    show "q = r"
    proof (insert prems, induct q, induct r)
      fix a b c d :: int
      assume neq: "b \<noteq> 0"  "d \<noteq> 0"
      assume 1: "Fract a b \<le> Fract c d" and 2: "Fract c d \<le> Fract a b"
      show "Fract a b = Fract c d"
      proof -
        from neq 1 have "(a * d) * (b * d) \<le> (c * b) * (b * d)"
          by (simp add: le_rat)
        also have "... \<le> (a * d) * (b * d)"
        proof -
          from neq 2 have "(c * b) * (d * b) \<le> (a * d) * (d * b)"
            by (simp add: le_rat)
          thus ?thesis by (simp only: mult_ac)
        qed
        finally have "(a * d) * (b * d) = (c * b) * (b * d)" .
        moreover from neq have "b * d \<noteq> 0" by simp
        ultimately have "a * d = c * b" by simp
        with neq show ?thesis by (simp add: eq_rat)
      qed
    qed
  next
    show "q \<le> q"
      by (induct q) (simp add: le_rat)
    show "(q < r) = (q \<le> r \<and> q \<noteq> r)"
      by (simp only: less_rat_def)
    show "q \<le> r \<or> r \<le> q"
      by (induct q, induct r)
         (simp add: le_rat mult_commute, rule linorder_linear)
  }
qed

end

instantiation rat :: "{distrib_lattice, abs_if, sgn_if}"
begin

definition
  abs_rat_def: "\<bar>q\<bar> = (if q < 0 then -q else (q::rat))"

lemma abs_rat: "\<bar>Fract a b\<bar> = Fract \<bar>a\<bar> \<bar>b\<bar>"
  by (auto simp add: abs_rat_def zabs_def Zero_rat_def less_rat not_less le_less minus_rat eq_rat zero_compare_simps)

definition
  sgn_rat_def: "sgn (q::rat) = (if q = 0 then 0 else if 0 < q then 1 else - 1)"

lemma sgn_rat: "sgn (Fract a b) = Fract (sgn a * sgn b) 1"
  unfolding Fract_of_int_eq
  by (auto simp: zsgn_def sgn_rat_def Zero_rat_def eq_rat less_rat)
    (auto simp: rat_number_collapse not_less le_less zero_less_mult_iff)

definition
  "(inf \<Colon> rat \<Rightarrow> rat \<Rightarrow> rat) = min"

definition
  "(sup \<Colon> rat \<Rightarrow> rat \<Rightarrow> rat) = max"

instance by intro_classes
  (auto simp add: abs_rat_def sgn_rat_def min_max.sup_inf_distrib1 inf_rat_def sup_rat_def)

end

instance rat :: ordered_field
proof
  fix q r s :: rat
  show "q \<le> r ==> s + q \<le> s + r"
  proof (induct q, induct r, induct s)
    fix a b c d e f :: int
    assume neq: "b \<noteq> 0"  "d \<noteq> 0"  "f \<noteq> 0"
    assume le: "Fract a b \<le> Fract c d"
    show "Fract e f + Fract a b \<le> Fract e f + Fract c d"
    proof -
      let ?F = "f * f" from neq have F: "0 < ?F"
        by (auto simp add: zero_less_mult_iff)
      from neq le have "(a * d) * (b * d) \<le> (c * b) * (b * d)"
        by (simp add: le_rat)
      with F have "(a * d) * (b * d) * ?F * ?F \<le> (c * b) * (b * d) * ?F * ?F"
        by (simp add: mult_le_cancel_right)
      with neq show ?thesis by (simp add: add_rat le_rat mult_ac int_distrib)
    qed
  qed
  show "q < r ==> 0 < s ==> s * q < s * r"
  proof (induct q, induct r, induct s)
    fix a b c d e f :: int
    assume neq: "b \<noteq> 0"  "d \<noteq> 0"  "f \<noteq> 0"
    assume le: "Fract a b < Fract c d"
    assume gt: "0 < Fract e f"
    show "Fract e f * Fract a b < Fract e f * Fract c d"
    proof -
      let ?E = "e * f" and ?F = "f * f"
      from neq gt have "0 < ?E"
        by (auto simp add: Zero_rat_def less_rat le_rat order_less_le eq_rat)
      moreover from neq have "0 < ?F"
        by (auto simp add: zero_less_mult_iff)
      moreover from neq le have "(a * d) * (b * d) < (c * b) * (b * d)"
        by (simp add: less_rat)
      ultimately have "(a * d) * (b * d) * ?E * ?F < (c * b) * (b * d) * ?E * ?F"
        by (simp add: mult_less_cancel_right)
      with neq show ?thesis
        by (simp add: less_rat mult_rat mult_ac)
    qed
  qed
qed auto

lemma Rat_induct_pos [case_names Fract, induct type: rat]:
  assumes step: "\<And>a b. 0 < b \<Longrightarrow> P (Fract a b)"
  shows "P q"
proof (cases q)
  have step': "\<And>a b. b < 0 \<Longrightarrow> P (Fract a b)"
  proof -
    fix a::int and b::int
    assume b: "b < 0"
    hence "0 < -b" by simp
    hence "P (Fract (-a) (-b))" by (rule step)
    thus "P (Fract a b)" by (simp add: order_less_imp_not_eq [OF b])
  qed
  case (Fract a b)
  thus "P q" by (force simp add: linorder_neq_iff step step')
qed

lemma zero_less_Fract_iff:
     "0 < b ==> (0 < Fract a b) = (0 < a)"
by (simp add: Zero_rat_def less_rat order_less_imp_not_eq2 zero_less_mult_iff)


subsection {* Arithmetic setup *}

use "rat_arith.ML"
declaration {* K rat_arith_setup *}


subsection {* Embedding from Rationals to other Fields *}

class field_char_0 = field + ring_char_0

subclass (in ordered_field) field_char_0 ..

context field_char_0
begin

definition of_rat :: "rat \<Rightarrow> 'a" where
  [code func del]: "of_rat q = contents (\<Union>(a,b) \<in> Rep_Rat q. {of_int a / of_int b})"

end

lemma of_rat_congruent:
  "(\<lambda>(a, b). {of_int a / of_int b :: 'a::field_char_0}) respects ratrel"
apply (rule congruent.intro)
apply (clarsimp simp add: nonzero_divide_eq_eq nonzero_eq_divide_eq)
apply (simp only: of_int_mult [symmetric])
done

lemma of_rat_rat: "b \<noteq> 0 \<Longrightarrow> of_rat (Fract a b) = of_int a / of_int b"
  unfolding Fract_def of_rat_def by (simp add: UN_ratrel of_rat_congruent)

lemma of_rat_0 [simp]: "of_rat 0 = 0"
by (simp add: Zero_rat_def of_rat_rat)

lemma of_rat_1 [simp]: "of_rat 1 = 1"
by (simp add: One_rat_def of_rat_rat)

lemma of_rat_add: "of_rat (a + b) = of_rat a + of_rat b"
by (induct a, induct b, simp add: add_rat of_rat_rat add_frac_eq)

lemma of_rat_minus: "of_rat (- a) = - of_rat a"
by (induct a, simp add: minus_rat of_rat_rat)

lemma of_rat_diff: "of_rat (a - b) = of_rat a - of_rat b"
by (simp only: diff_minus of_rat_add of_rat_minus)

lemma of_rat_mult: "of_rat (a * b) = of_rat a * of_rat b"
apply (induct a, induct b, simp add: mult_rat of_rat_rat)
apply (simp add: divide_inverse nonzero_inverse_mult_distrib mult_ac)
done

lemma nonzero_of_rat_inverse:
  "a \<noteq> 0 \<Longrightarrow> of_rat (inverse a) = inverse (of_rat a)"
apply (rule inverse_unique [symmetric])
apply (simp add: of_rat_mult [symmetric])
done

lemma of_rat_inverse:
  "(of_rat (inverse a)::'a::{field_char_0,division_by_zero}) =
   inverse (of_rat a)"
by (cases "a = 0", simp_all add: nonzero_of_rat_inverse)

lemma nonzero_of_rat_divide:
  "b \<noteq> 0 \<Longrightarrow> of_rat (a / b) = of_rat a / of_rat b"
by (simp add: divide_inverse of_rat_mult nonzero_of_rat_inverse)

lemma of_rat_divide:
  "(of_rat (a / b)::'a::{field_char_0,division_by_zero})
   = of_rat a / of_rat b"
by (cases "b = 0", simp_all add: nonzero_of_rat_divide)

lemma of_rat_power:
  "(of_rat (a ^ n)::'a::{field_char_0,recpower}) = of_rat a ^ n"
by (induct n) (simp_all add: of_rat_mult power_Suc)

lemma of_rat_eq_iff [simp]: "(of_rat a = of_rat b) = (a = b)"
apply (induct a, induct b)
apply (simp add: of_rat_rat eq_rat)
apply (simp add: nonzero_divide_eq_eq nonzero_eq_divide_eq)
apply (simp only: of_int_mult [symmetric] of_int_eq_iff)
done

lemmas of_rat_eq_0_iff [simp] = of_rat_eq_iff [of _ 0, simplified]

lemma of_rat_eq_id [simp]: "of_rat = (id :: rat \<Rightarrow> rat)"
proof
  fix a
  show "of_rat a = id a"
  by (induct a)
     (simp add: of_rat_rat divide_rat Fract_of_int_eq [symmetric])
qed

text{*Collapse nested embeddings*}
lemma of_rat_of_nat_eq [simp]: "of_rat (of_nat n) = of_nat n"
by (induct n) (simp_all add: of_rat_add)

lemma of_rat_of_int_eq [simp]: "of_rat (of_int z) = of_int z"
by (cases z rule: int_diff_cases, simp add: of_rat_diff)

lemma of_rat_number_of_eq [simp]:
  "of_rat (number_of w) = (number_of w :: 'a::{number_ring,field_char_0})"
by (simp add: number_of_eq)

lemmas zero_rat = Zero_rat_def
lemmas one_rat = One_rat_def

abbreviation
  rat_of_nat :: "nat \<Rightarrow> rat"
where
  "rat_of_nat \<equiv> of_nat"

abbreviation
  rat_of_int :: "int \<Rightarrow> rat"
where
  "rat_of_int \<equiv> of_int"


subsection {* Implementation of rational numbers as pairs of integers *}

lemma INum_Fract [simp]: "INum = split Fract"
  by (auto simp add: expand_fun_eq INum_def Fract_of_int_quotient)

lemma split_Fract_normNum [simp]: "split Fract (normNum (k, l)) = Fract k l"
  unfolding INum_Fract [symmetric] normNum by simp

lemma [code]:
  "of_rat (Fract k l) = (if l \<noteq> 0 then of_int k / of_int l else 0)"
  by (cases "l = 0") (simp_all add: rat_number_collapse of_rat_rat)

instantiation rat :: eq
begin

definition [code func del]: "eq_class.eq (r\<Colon>rat) s \<longleftrightarrow> r - s = 0"

instance by default (simp add: eq_rat_def)

lemma rat_eq_code [code]: "eq_class.eq (Fract k l) (Fract r s) \<longleftrightarrow> eq_class.eq (normNum (k, l)) (normNum (r, s))"
  by (simp add: eq INum_normNum_iff [where ?'a = rat, symmetric])

end

lemma rat_less_eq_code [code]: "Fract k l \<le> Fract r s \<longleftrightarrow> normNum (k, l) \<le>\<^sub>N normNum (r, s)"
proof -
  have "normNum (k, l) \<le>\<^sub>N normNum (r, s) \<longleftrightarrow> split Fract (normNum (k, l)) \<le> split Fract (normNum (r, s))" 
    by (simp add: INum_Fract [symmetric] del: INum_Fract normNum)
  also have "\<dots> = (Fract k l \<le> Fract r s)" by simp
  finally show ?thesis by simp
qed

lemma rat_less_code [code]: "Fract k l < Fract r s \<longleftrightarrow> normNum (k, l) <\<^sub>N normNum (r, s)"
proof -
  have "normNum (k, l) <\<^sub>N normNum (r, s) \<longleftrightarrow> split Fract (normNum (k, l)) < split Fract (normNum (r, s))" 
    by (simp add: INum_Fract [symmetric] del: INum_Fract normNum)
  also have "\<dots> = (Fract k l < Fract r s)" by simp
  finally show ?thesis by simp
qed

lemma rat_add_code [code]: "Fract k l + Fract r s = split Fract ((k, l) +\<^sub>N (r, s))"
  by (simp add: INum_Fract [symmetric] del: INum_Fract, simp)

lemma rat_mul_code [code]: "Fract k l * Fract r s = split Fract ((k, l) *\<^sub>N (r, s))"
  by (simp add: INum_Fract [symmetric] del: INum_Fract, simp)

lemma rat_neg_code [code]: "- Fract k l = split Fract (~\<^sub>N (k, l))"
  by (simp add: INum_Fract [symmetric] del: INum_Fract, simp)

lemma rat_sub_code [code]: "Fract k l - Fract r s = split Fract ((k, l) -\<^sub>N (r, s))"
  by (simp add: INum_Fract [symmetric] del: INum_Fract, simp)

lemma rat_inv_code [code]: "inverse (Fract k l) = split Fract (Ninv (k, l))"
  by (simp add: INum_Fract [symmetric] del: INum_Fract, simp add: divide_rat_def)

lemma rat_div_code [code]: "Fract k l / Fract r s = split Fract ((k, l) \<div>\<^sub>N (r, s))"
  by (simp add: INum_Fract [symmetric] del: INum_Fract, simp)

text {* Setup for SML code generator *}

types_code
  rat ("(int */ int)")
attach (term_of) {*
fun term_of_rat (p, q) =
  let
    val rT = Type ("Rational.rat", [])
  in
    if q = 1 orelse p = 0 then HOLogic.mk_number rT p
    else @{term "op / \<Colon> rat \<Rightarrow> rat \<Rightarrow> rat"} $
      HOLogic.mk_number rT p $ HOLogic.mk_number rT q
  end;
*}
attach (test) {*
fun gen_rat i =
  let
    val p = random_range 0 i;
    val q = random_range 1 (i + 1);
    val g = Integer.gcd p q;
    val p' = p div g;
    val q' = q div g;
    val r = (if one_of [true, false] then p' else ~ p',
      if p' = 0 then 0 else q')
  in
    (r, fn () => term_of_rat r)
  end;
*}

consts_code
  Fract ("(_,/ _)")

consts_code
  "of_int :: int \<Rightarrow> rat" ("\<module>rat'_of'_int")
attach {*
fun rat_of_int 0 = (0, 0)
  | rat_of_int i = (i, 1);
*}

end
