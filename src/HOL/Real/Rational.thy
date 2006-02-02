(*  Title: HOL/Library/Rational.thy
    ID:    $Id$
    Author: Markus Wenzel, TU Muenchen
*)

header {* Rational numbers *}

theory Rational
imports Main
uses ("rat_arith.ML")
begin

subsection {* Rational numbers *}

subsubsection {* Equivalence of fractions *}

constdefs
  fraction :: "(int \<times> int) set"
   "fraction \<equiv> {x. snd x \<noteq> 0}"

  ratrel :: "((int \<times> int) \<times> (int \<times> int)) set"
   "ratrel \<equiv> {(x,y). snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x}"

lemma fraction_iff [simp]: "(x \<in> fraction) = (snd x \<noteq> 0)"
by (simp add: fraction_def)

lemma ratrel_iff [simp]:
  "((x,y) \<in> ratrel) =
   (snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x)"
by (simp add: ratrel_def)

lemma refl_ratrel: "refl fraction ratrel"
by (auto simp add: refl_def fraction_def ratrel_def)

lemma sym_ratrel: "sym ratrel"
by (simp add: ratrel_def sym_def)

lemma trans_ratrel_lemma:
  assumes 1: "a * b' = a' * b"
  assumes 2: "a' * b'' = a'' * b'"
  assumes 3: "b' \<noteq> (0::int)"
  shows "a * b'' = a'' * b"
proof -
  have "b' * (a * b'') = b'' * (a * b')" by simp
  also note 1
  also have "b'' * (a' * b) = b * (a' * b'')" by simp
  also note 2
  also have "b * (a'' * b') = b' * (a'' * b)" by simp
  finally have "b' * (a * b'') = b' * (a'' * b)" .
  with 3 show "a * b'' = a'' * b" by simp
qed

lemma trans_ratrel: "trans ratrel"
by (auto simp add: trans_def elim: trans_ratrel_lemma)

lemma equiv_ratrel: "equiv fraction ratrel"
by (rule equiv.intro [OF refl_ratrel sym_ratrel trans_ratrel])

lemmas equiv_ratrel_iff [iff] = eq_equiv_class_iff [OF equiv_ratrel]

lemma equiv_ratrel_iff2:
  "\<lbrakk>snd x \<noteq> 0; snd y \<noteq> 0\<rbrakk>
    \<Longrightarrow> (ratrel `` {x} = ratrel `` {y}) = ((x,y) \<in> ratrel)"
by (rule eq_equiv_class_iff [OF equiv_ratrel], simp_all)


subsubsection {* The type of rational numbers *}

typedef (Rat) rat = "fraction//ratrel"
proof
  have "(0,1) \<in> fraction" by (simp add: fraction_def)
  thus "ratrel``{(0,1)} \<in> fraction//ratrel" by (rule quotientI)
qed

lemma ratrel_in_Rat [simp]: "snd x \<noteq> 0 \<Longrightarrow> ratrel``{x} \<in> Rat"
by (simp add: Rat_def quotientI)

declare Abs_Rat_inject [simp]  Abs_Rat_inverse [simp]


constdefs
  Fract :: "int \<Rightarrow> int \<Rightarrow> rat"
  "Fract a b \<equiv> Abs_Rat (ratrel``{(a,b)})"

theorem Rat_cases [case_names Fract, cases type: rat]:
  "(!!a b. q = Fract a b ==> b \<noteq> 0 ==> C) ==> C"
by (cases q, clarsimp simp add: Fract_def Rat_def fraction_def quotient_def)

theorem Rat_induct [case_names Fract, induct type: rat]:
    "(!!a b. b \<noteq> 0 ==> P (Fract a b)) ==> P q"
  by (cases q) simp


subsubsection {* Congruence lemmas *}

lemma add_congruent2:
     "(\<lambda>x y. ratrel``{(fst x * snd y + fst y * snd x, snd x * snd y)})
      respects2 ratrel"
apply (rule equiv_ratrel [THEN congruent2_commuteI])
apply (simp_all add: left_distrib)
done

lemma minus_congruent:
  "(\<lambda>x. ratrel``{(- fst x, snd x)}) respects ratrel"
by (simp add: congruent_def)

lemma mult_congruent2:
  "(\<lambda>x y. ratrel``{(fst x * fst y, snd x * snd y)}) respects2 ratrel"
by (rule equiv_ratrel [THEN congruent2_commuteI], simp_all)

lemma inverse_congruent:
  "(\<lambda>x. ratrel``{if fst x=0 then (0,1) else (snd x, fst x)}) respects ratrel"
by (auto simp add: congruent_def mult_commute)

lemma le_congruent2:
  "(\<lambda>x y. (fst x * snd y)*(snd x * snd y) \<le> (fst y * snd x)*(snd x * snd y))
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

lemma All_equiv_class:
  "equiv A r ==> f respects r ==> a \<in> A
    ==> (\<forall>x \<in> r``{a}. f x) = f a"
apply safe
apply (drule (1) equiv_class_self)
apply simp
apply (drule (1) congruent.congruent)
apply simp
done

lemma congruent2_implies_congruent_All:
  "equiv A1 r1 ==> equiv A2 r2 ==> congruent2 r1 r2 f ==> a \<in> A2 ==>
    congruent r1 (\<lambda>x1. \<forall>x2 \<in> r2``{a}. f x1 x2)"
  apply (unfold congruent_def)
  apply clarify
  apply (rule equiv_type [THEN subsetD, THEN SigmaE2], assumption+)
  apply (simp add: UN_equiv_class congruent2_implies_congruent)
  apply (unfold congruent2_def equiv_def refl_def)
  apply (blast del: equalityI)
  done

lemma All_equiv_class2:
  "equiv A1 r1 ==> equiv A2 r2 ==> congruent2 r1 r2 f ==> a1 \<in> A1 ==> a2 \<in> A2
    ==> (\<forall>x1 \<in> r1``{a1}. \<forall>x2 \<in> r2``{a2}. f x1 x2) = f a1 a2"
  by (simp add: All_equiv_class congruent2_implies_congruent
    congruent2_implies_congruent_All)

lemmas UN_ratrel = UN_equiv_class [OF equiv_ratrel]
lemmas UN_ratrel2 = UN_equiv_class2 [OF equiv_ratrel equiv_ratrel]
lemmas All_ratrel2 = All_equiv_class2 [OF equiv_ratrel equiv_ratrel]


subsubsection {* Standard operations on rational numbers *}

instance rat :: "{ord, zero, one, plus, times, minus, inverse}" ..

defs (overloaded)
  Zero_rat_def:  "0 == Fract 0 1"
  One_rat_def:   "1 == Fract 1 1"

  add_rat_def:
   "q + r ==
       Abs_Rat (\<Union>x \<in> Rep_Rat q. \<Union>y \<in> Rep_Rat r.
           ratrel``{(fst x * snd y + fst y * snd x, snd x * snd y)})"

  minus_rat_def:
    "- q == Abs_Rat (\<Union>x \<in> Rep_Rat q. ratrel``{(- fst x, snd x)})"

  diff_rat_def:  "q - r == q + - (r::rat)"

  mult_rat_def:
   "q * r ==
       Abs_Rat (\<Union>x \<in> Rep_Rat q. \<Union>y \<in> Rep_Rat r.
           ratrel``{(fst x * fst y, snd x * snd y)})"

  inverse_rat_def:
    "inverse q ==
        Abs_Rat (\<Union>x \<in> Rep_Rat q.
            ratrel``{if fst x=0 then (0,1) else (snd x, fst x)})"

  divide_rat_def:  "q / r == q * inverse (r::rat)"

  le_rat_def:
   "q \<le> (r::rat) ==
    \<forall>x \<in> Rep_Rat q. \<forall>y \<in> Rep_Rat r.
        (fst x * snd y)*(snd x * snd y) \<le> (fst y * snd x)*(snd x * snd y)"

  less_rat_def: "(z < (w::rat)) == (z \<le> w & z \<noteq> w)"

  abs_rat_def: "\<bar>q\<bar> == if q < 0 then -q else (q::rat)"

lemma zero_rat: "0 = Fract 0 1"
by (simp add: Zero_rat_def)

lemma one_rat: "1 = Fract 1 1"
by (simp add: One_rat_def)

theorem eq_rat: "b \<noteq> 0 ==> d \<noteq> 0 ==>
  (Fract a b = Fract c d) = (a * d = c * b)"
by (simp add: Fract_def)

theorem add_rat: "b \<noteq> 0 ==> d \<noteq> 0 ==>
  Fract a b + Fract c d = Fract (a * d + c * b) (b * d)"
by (simp add: Fract_def add_rat_def add_congruent2 UN_ratrel2)

theorem minus_rat: "b \<noteq> 0 ==> -(Fract a b) = Fract (-a) b"
by (simp add: Fract_def minus_rat_def minus_congruent UN_ratrel)

theorem diff_rat: "b \<noteq> 0 ==> d \<noteq> 0 ==>
    Fract a b - Fract c d = Fract (a * d - c * b) (b * d)"
by (simp add: diff_rat_def add_rat minus_rat)

theorem mult_rat: "b \<noteq> 0 ==> d \<noteq> 0 ==>
  Fract a b * Fract c d = Fract (a * c) (b * d)"
by (simp add: Fract_def mult_rat_def mult_congruent2 UN_ratrel2)

theorem inverse_rat: "a \<noteq> 0 ==> b \<noteq> 0 ==>
  inverse (Fract a b) = Fract b a"
by (simp add: Fract_def inverse_rat_def inverse_congruent UN_ratrel)

theorem divide_rat: "c \<noteq> 0 ==> b \<noteq> 0 ==> d \<noteq> 0 ==>
  Fract a b / Fract c d = Fract (a * d) (b * c)"
by (simp add: divide_rat_def inverse_rat mult_rat)

theorem le_rat: "b \<noteq> 0 ==> d \<noteq> 0 ==>
  (Fract a b \<le> Fract c d) = ((a * d) * (b * d) \<le> (c * b) * (b * d))"
by (simp add: Fract_def le_rat_def le_congruent2 All_ratrel2)

theorem less_rat: "b \<noteq> 0 ==> d \<noteq> 0 ==>
    (Fract a b < Fract c d) = ((a * d) * (b * d) < (c * b) * (b * d))"
by (simp add: less_rat_def le_rat eq_rat order_less_le)

theorem abs_rat: "b \<noteq> 0 ==> \<bar>Fract a b\<bar> = Fract \<bar>a\<bar> \<bar>b\<bar>"
  by (simp add: abs_rat_def minus_rat zero_rat less_rat eq_rat)
     (auto simp add: mult_less_0_iff zero_less_mult_iff order_le_less
                split: abs_split)


subsubsection {* The ordered field of rational numbers *}

lemma rat_add_assoc: "(q + r) + s = q + (r + (s::rat))"
  by (induct q, induct r, induct s)
     (simp add: add_rat add_ac mult_ac int_distrib)

lemma rat_add_0: "0 + q = (q::rat)"
  by (induct q) (simp add: zero_rat add_rat)

lemma rat_left_minus: "(-q) + q = (0::rat)"
  by (induct q) (simp add: zero_rat minus_rat add_rat eq_rat)


instance rat :: field
proof
  fix q r s :: rat
  show "(q + r) + s = q + (r + s)"
    by (induct q, induct r, induct s)
       (simp add: add_rat add_ac mult_ac int_distrib)
  show "q + r = r + q"
    by (induct q, induct r) (simp add: add_rat add_ac mult_ac)
  show "0 + q = q"
    by (induct q) (simp add: zero_rat add_rat)
  show "(-q) + q = 0"
    by (induct q) (simp add: zero_rat minus_rat add_rat eq_rat)
  show "q - r = q + (-r)"
    by (induct q, induct r) (simp add: add_rat minus_rat diff_rat)
  show "(q * r) * s = q * (r * s)"
    by (induct q, induct r, induct s) (simp add: mult_rat mult_ac)
  show "q * r = r * q"
    by (induct q, induct r) (simp add: mult_rat mult_ac)
  show "1 * q = q"
    by (induct q) (simp add: one_rat mult_rat)
  show "(q + r) * s = q * s + r * s"
    by (induct q, induct r, induct s)
       (simp add: add_rat mult_rat eq_rat int_distrib)
  show "q \<noteq> 0 ==> inverse q * q = 1"
    by (induct q) (simp add: inverse_rat mult_rat one_rat zero_rat eq_rat)
  show "q / r = q * inverse r"
    by (simp add: divide_rat_def)
  show "0 \<noteq> (1::rat)"
    by (simp add: zero_rat one_rat eq_rat)
qed

instance rat :: linorder
proof
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
        by (auto simp add: zero_rat less_rat le_rat order_less_le eq_rat)
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
  show "\<bar>q\<bar> = (if q < 0 then -q else q)"
    by (simp only: abs_rat_def)
qed

instance rat :: division_by_zero
proof
  show "inverse 0 = (0::rat)"
    by (simp add: zero_rat Fract_def inverse_rat_def
                  inverse_congruent UN_ratrel)
qed


subsection {* Various Other Results *}

lemma minus_rat_cancel [simp]: "b \<noteq> 0 ==> Fract (-a) (-b) = Fract a b"
by (simp add: eq_rat)

theorem Rat_induct_pos [case_names Fract, induct type: rat]:
  assumes step: "!!a b. 0 < b ==> P (Fract a b)"
    shows "P q"
proof (cases q)
  have step': "!!a b. b < 0 ==> P (Fract a b)"
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
by (simp add: zero_rat less_rat order_less_imp_not_eq2 zero_less_mult_iff)

lemma Fract_add_one: "n \<noteq> 0 ==> Fract (m + n) n = Fract m n + 1"
apply (insert add_rat [of concl: m n 1 1])
apply (simp add: one_rat  [symmetric])
done

lemma Fract_of_nat_eq: "Fract (of_nat k) 1 = of_nat k"
apply (induct k)
apply (simp add: zero_rat)
apply (simp add: Fract_add_one)
done

lemma Fract_of_int_eq: "Fract k 1 = of_int k"
proof (cases k rule: int_cases)
  case (nonneg n)
    thus ?thesis by (simp add: int_eq_of_nat Fract_of_nat_eq)
next
  case (neg n)
    hence "Fract k 1 = - (Fract (of_nat (Suc n)) 1)"
      by (simp only: minus_rat int_eq_of_nat)
    also have "... =  - (of_nat (Suc n))"
      by (simp only: Fract_of_nat_eq)
    finally show ?thesis
      by (simp add: only: prems int_eq_of_nat of_int_minus of_int_of_nat_eq)
qed


subsection {* Numerals and Arithmetic *}

instance rat :: number ..

defs (overloaded)
  rat_number_of_def: "(number_of w :: rat) == of_int (Rep_Bin w)"
    --{*the type constraint is essential!*}

instance rat :: number_ring
by (intro_classes, simp add: rat_number_of_def) 

declare diff_rat_def [symmetric]

use "rat_arith.ML"

setup rat_arith_setup

end
