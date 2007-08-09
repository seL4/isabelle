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

definition
  fraction :: "(int \<times> int) set" where
  "fraction = {x. snd x \<noteq> 0}"

definition
  ratrel :: "((int \<times> int) \<times> (int \<times> int)) set" where
  "ratrel = {(x,y). snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x}"

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


definition
  Fract :: "int \<Rightarrow> int \<Rightarrow> rat" where
  [code func del]: "Fract a b = Abs_Rat (ratrel``{(a,b)})"

lemma Fract_zero:
  "Fract k 0 = Fract l 0"
  by (simp add: Fract_def ratrel_def)

theorem Rat_cases [case_names Fract, cases type: rat]:
    "(!!a b. q = Fract a b ==> b \<noteq> 0 ==> C) ==> C"
  by (cases q) (clarsimp simp add: Fract_def Rat_def fraction_def quotient_def)

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
  "(\<lambda>x y. {(fst x * snd y)*(snd x * snd y) \<le> (fst y * snd x)*(snd x * snd y)})
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

lemmas UN_ratrel = UN_equiv_class [OF equiv_ratrel]
lemmas UN_ratrel2 = UN_equiv_class2 [OF equiv_ratrel equiv_ratrel]


subsubsection {* Standard operations on rational numbers *}

instance rat :: zero
  Zero_rat_def: "0 == Fract 0 1" ..
lemmas [code func del] = Zero_rat_def

instance rat :: one
  One_rat_def: "1 == Fract 1 1" ..
lemmas [code func del] = One_rat_def

instance rat :: plus
  add_rat_def:
   "q + r ==
       Abs_Rat (\<Union>x \<in> Rep_Rat q. \<Union>y \<in> Rep_Rat r.
           ratrel``{(fst x * snd y + fst y * snd x, snd x * snd y)})" ..
lemmas [code func del] = add_rat_def

instance rat :: minus
  minus_rat_def:
    "- q == Abs_Rat (\<Union>x \<in> Rep_Rat q. ratrel``{(- fst x, snd x)})"
  diff_rat_def:  "q - r == q + - (r::rat)" ..
lemmas [code func del] = minus_rat_def diff_rat_def

instance rat :: times
  mult_rat_def:
   "q * r ==
       Abs_Rat (\<Union>x \<in> Rep_Rat q. \<Union>y \<in> Rep_Rat r.
           ratrel``{(fst x * fst y, snd x * snd y)})" ..
lemmas [code func del] = mult_rat_def

instance rat :: inverse
  inverse_rat_def:
    "inverse q ==
        Abs_Rat (\<Union>x \<in> Rep_Rat q.
            ratrel``{if fst x=0 then (0,1) else (snd x, fst x)})"
  divide_rat_def:  "q / r == q * inverse (r::rat)" ..
lemmas [code func del] = inverse_rat_def divide_rat_def

instance rat :: ord
  le_rat_def:
   "q \<le> r == contents (\<Union>x \<in> Rep_Rat q. \<Union>y \<in> Rep_Rat r.
      {(fst x * snd y)*(snd x * snd y) \<le> (fst y * snd x)*(snd x * snd y)})"
  less_rat_def: "(z < (w::rat)) == (z \<le> w & z \<noteq> w)" ..
lemmas [code func del] = le_rat_def less_rat_def

instance rat :: abs
  abs_rat_def: "\<bar>q\<bar> == if q < 0 then -q else (q::rat)" ..

instance rat :: power ..

primrec (rat)
  rat_power_0:   "q ^ 0       = 1"
  rat_power_Suc: "q ^ (Suc n) = (q::rat) * (q ^ n)"

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
by (simp add: Fract_def le_rat_def le_congruent2 UN_ratrel2)

theorem less_rat: "b \<noteq> 0 ==> d \<noteq> 0 ==>
    (Fract a b < Fract c d) = ((a * d) * (b * d) < (c * b) * (b * d))"
by (simp add: less_rat_def le_rat eq_rat order_less_le)

theorem abs_rat: "b \<noteq> 0 ==> \<bar>Fract a b\<bar> = Fract \<bar>a\<bar> \<bar>b\<bar>"
  by (simp add: abs_rat_def minus_rat Zero_rat_def less_rat eq_rat)
     (auto simp add: mult_less_0_iff zero_less_mult_iff order_le_less
                split: abs_split)


subsubsection {* The ordered field of rational numbers *}

instance rat :: field
proof
  fix q r s :: rat
  show "(q + r) + s = q + (r + s)"
    by (induct q, induct r, induct s)
       (simp add: add_rat add_ac mult_ac int_distrib)
  show "q + r = r + q"
    by (induct q, induct r) (simp add: add_rat add_ac mult_ac)
  show "0 + q = q"
    by (induct q) (simp add: Zero_rat_def add_rat)
  show "(-q) + q = 0"
    by (induct q) (simp add: Zero_rat_def minus_rat add_rat eq_rat)
  show "q - r = q + (-r)"
    by (induct q, induct r) (simp add: add_rat minus_rat diff_rat)
  show "(q * r) * s = q * (r * s)"
    by (induct q, induct r, induct s) (simp add: mult_rat mult_ac)
  show "q * r = r * q"
    by (induct q, induct r) (simp add: mult_rat mult_ac)
  show "1 * q = q"
    by (induct q) (simp add: One_rat_def mult_rat)
  show "(q + r) * s = q * s + r * s"
    by (induct q, induct r, induct s)
       (simp add: add_rat mult_rat eq_rat int_distrib)
  show "q \<noteq> 0 ==> inverse q * q = 1"
    by (induct q) (simp add: inverse_rat mult_rat One_rat_def Zero_rat_def eq_rat)
  show "q / r = q * inverse r"
    by (simp add: divide_rat_def)
  show "0 \<noteq> (1::rat)"
    by (simp add: Zero_rat_def One_rat_def eq_rat)
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

instance rat :: distrib_lattice
  "inf r s \<equiv> min r s"
  "sup r s \<equiv> max r s"
  by default (auto simp add: min_max.sup_inf_distrib1 inf_rat_def sup_rat_def)

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
  show "\<bar>q\<bar> = (if q < 0 then -q else q)"
    by (simp only: abs_rat_def)
qed auto

instance rat :: division_by_zero
proof
  show "inverse 0 = (0::rat)"
    by (simp add: Zero_rat_def Fract_def inverse_rat_def
                  inverse_congruent UN_ratrel)
qed

instance rat :: recpower
proof
  fix q :: rat
  fix n :: nat
  show "q ^ 0 = 1" by simp
  show "q ^ (Suc n) = q * (q ^ n)" by simp
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
by (simp add: Zero_rat_def less_rat order_less_imp_not_eq2 zero_less_mult_iff)

lemma Fract_add_one: "n \<noteq> 0 ==> Fract (m + n) n = Fract m n + 1"
apply (insert add_rat [of concl: m n 1 1])
apply (simp add: One_rat_def [symmetric])
done

lemma of_nat_rat: "of_nat k = Fract (of_nat k) 1"
by (induct k) (simp_all add: Zero_rat_def One_rat_def add_rat)

lemma of_int_rat: "of_int k = Fract k 1"
by (cases k rule: int_diff_cases, simp add: of_nat_rat diff_rat)

lemma Fract_of_nat_eq: "Fract (of_nat k) 1 = of_nat k"
by (rule of_nat_rat [symmetric])

lemma Fract_of_int_eq: "Fract k 1 = of_int k"
by (rule of_int_rat [symmetric])

lemma Fract_of_int_quotient: "Fract k l = (if l = 0 then Fract 1 0 else of_int k / of_int l)"
by (auto simp add: Fract_zero Fract_of_int_eq [symmetric] divide_rat)


subsection {* Numerals and Arithmetic *}

instance rat :: number
  rat_number_of_def: "(number_of w :: rat) \<equiv> of_int w" ..

instance rat :: number_ring
  by default (simp add: rat_number_of_def) 

use "rat_arith.ML"
declaration {* K rat_arith_setup *}


subsection {* Embedding from Rationals to other Fields *}

class field_char_0 = field + ring_char_0

instance ordered_field < field_char_0 ..

definition
  of_rat :: "rat \<Rightarrow> 'a::field_char_0"
where
  [code func del]: "of_rat q = contents (\<Union>(a,b) \<in> Rep_Rat q. {of_int a / of_int b})"

lemma of_rat_congruent:
  "(\<lambda>(a, b). {of_int a / of_int b::'a::field_char_0}) respects ratrel"
apply (rule congruent.intro)
apply (clarsimp simp add: nonzero_divide_eq_eq nonzero_eq_divide_eq)
apply (simp only: of_int_mult [symmetric])
done

lemma of_rat_rat:
  "b \<noteq> 0 \<Longrightarrow> of_rat (Fract a b) = of_int a / of_int b"
unfolding Fract_def of_rat_def
by (simp add: UN_ratrel of_rat_congruent)

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

end
