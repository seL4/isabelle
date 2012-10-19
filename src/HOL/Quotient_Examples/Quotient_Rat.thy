(*  Title:      HOL/Quotient_Examples/Quotient_Rat.thy
    Author:     Cezary Kaliszyk

Rational numbers defined with the quotient package, based on 'HOL/Rat.thy' by Makarius.
*)

theory Quotient_Rat imports Archimedean_Field
  "~~/src/HOL/Library/Quotient_Product"
begin

definition
  ratrel :: "(int \<times> int) \<Rightarrow> (int \<times> int) \<Rightarrow> bool" (infix "\<approx>" 50)
where
  [simp]: "x \<approx> y \<longleftrightarrow> snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x"

lemma ratrel_equivp:
  "part_equivp ratrel"
proof (auto intro!: part_equivpI reflpI sympI transpI exI[of _ "1 :: int"])
  fix a b c d e f :: int
  assume nz: "d \<noteq> 0" "b \<noteq> 0"
  assume y: "a * d = c * b"
  assume x: "c * f = e * d"
  then have "c * b * f = e * d * b" using nz by simp
  then have "a * d * f = e * d * b" using y by simp
  then show "a * f = e * b" using nz by simp
qed

quotient_type rat = "int \<times> int" / partial: ratrel
 using ratrel_equivp .

instantiation rat :: "{zero, one, plus, uminus, minus, times, ord, abs_if, sgn_if}"
begin

quotient_definition
  "0 \<Colon> rat" is "(0\<Colon>int, 1\<Colon>int)" by simp

quotient_definition
  "1 \<Colon> rat" is "(1\<Colon>int, 1\<Colon>int)" by simp

fun times_rat_raw where
  "times_rat_raw (a :: int, b :: int) (c, d) = (a * c, b * d)"

quotient_definition
  "(op *) :: (rat \<Rightarrow> rat \<Rightarrow> rat)" is times_rat_raw by (auto simp add: mult_assoc mult_left_commute)

fun plus_rat_raw where
  "plus_rat_raw (a :: int, b :: int) (c, d) = (a * d + c * b, b * d)"

quotient_definition
  "(op +) :: (rat \<Rightarrow> rat \<Rightarrow> rat)" is plus_rat_raw 
  by (auto simp add: mult_commute mult_left_commute int_distrib(2))

fun uminus_rat_raw where
  "uminus_rat_raw (a :: int, b :: int) = (-a, b)"

quotient_definition
  "(uminus \<Colon> (rat \<Rightarrow> rat))" is "uminus_rat_raw" by fastforce

definition
  minus_rat_def: "a - b = a + (-b\<Colon>rat)"

fun le_rat_raw where
  "le_rat_raw (a :: int, b) (c, d) \<longleftrightarrow> (a * d) * (b * d) \<le> (c * b) * (b * d)"

quotient_definition
  "(op \<le>) :: rat \<Rightarrow> rat \<Rightarrow> bool" is "le_rat_raw"
proof -
  {
    fix a b c d e f g h :: int
    assume "a * f * (b * f) \<le> e * b * (b * f)"
    then have le: "a * f * b * f \<le> e * b * b * f" by simp
    assume nz: "b \<noteq> 0" "d \<noteq> 0" "f \<noteq> 0" "h \<noteq> 0"
    then have b2: "b * b > 0"
      by (metis linorder_neqE_linordered_idom mult_eq_0_iff not_square_less_zero)
    have f2: "f * f > 0" using nz(3)
      by (metis linorder_neqE_linordered_idom mult_eq_0_iff not_square_less_zero)
    assume eq: "a * d = c * b" "e * h = g * f"
    have "a * f * b * f * d * d \<le> e * b * b * f * d * d" using le nz(2)
      by (metis linorder_le_cases mult_right_mono mult_right_mono_neg)
    then have "c * f * f * d * (b * b) \<le> e * f * d * d * (b * b)" using eq
      by (metis (no_types) mult_assoc mult_commute)
    then have "c * f * f * d \<le> e * f * d * d" using b2
      by (metis leD linorder_le_less_linear mult_strict_right_mono)
    then have "c * f * f * d * h * h \<le> e * f * d * d * h * h" using nz(4)
      by (metis linorder_le_cases mult_right_mono mult_right_mono_neg)
    then have "c * h * (d * h) * (f * f) \<le> g * d * (d * h) * (f * f)" using eq
      by (metis (no_types) mult_assoc mult_commute)
    then have "c * h * (d * h) \<le> g * d * (d * h)" using f2
      by (metis leD linorder_le_less_linear mult_strict_right_mono)
  }
  then show "\<And>x y xa ya. x \<approx> y \<Longrightarrow> xa \<approx> ya \<Longrightarrow> le_rat_raw x xa = le_rat_raw y ya" by auto
qed

definition
  less_rat_def: "(z\<Colon>rat) < w = (z \<le> w \<and> z \<noteq> w)"

definition
  rabs_rat_def: "\<bar>i\<Colon>rat\<bar> = (if i < 0 then - i else i)"

definition
  sgn_rat_def: "sgn (i\<Colon>rat) = (if i = 0 then 0 else if 0 < i then 1 else - 1)"

instance by intro_classes
  (auto simp add: rabs_rat_def sgn_rat_def)

end

definition
  Fract_raw :: "int \<Rightarrow> int \<Rightarrow> (int \<times> int)"
where [simp]: "Fract_raw a b = (if b = 0 then (0, 1) else (a, b))"

quotient_definition "Fract :: int \<Rightarrow> int \<Rightarrow> rat" is
  Fract_raw by simp

lemmas [simp] = Respects_def

(* FIXME: (partiality_)descending raises exception TYPE_MATCH

instantiation rat :: comm_ring_1
begin

instance proof
  fix a b c :: rat
  show "a * b * c = a * (b * c)"
    by partiality_descending auto
  show "a * b = b * a"
    by partiality_descending auto
  show "1 * a = a"
    by partiality_descending auto
  show "a + b + c = a + (b + c)"
    by partiality_descending (auto simp add: mult_commute distrib_left)
  show "a + b = b + a"
    by partiality_descending auto
  show "0 + a = a"
    by partiality_descending auto
  show "- a + a = 0"
    by partiality_descending auto
  show "a - b = a + - b"
    by (simp add: minus_rat_def)
  show "(a + b) * c = a * c + b * c"
    by partiality_descending (auto simp add: mult_commute distrib_left)
  show "(0 :: rat) \<noteq> (1 :: rat)"
    by partiality_descending auto
qed

end

lemma add_one_Fract: "1 + Fract (int k) 1 = Fract (1 + int k) 1"
  by descending auto

lemma of_nat_rat: "of_nat k = Fract (of_nat k) 1"
  apply (induct k)
  apply (simp add: zero_rat_def Fract_def)
  apply (simp add: add_one_Fract)
  done

lemma of_int_rat: "of_int k = Fract k 1"
  apply (cases k rule: int_diff_cases)
  apply (auto simp add: of_nat_rat minus_rat_def)
  apply descending
  apply auto
  done

instantiation rat :: field_inverse_zero begin

fun rat_inverse_raw where
  "rat_inverse_raw (a :: int, b :: int) = (if a = 0 then (0, 1) else (b, a))"

quotient_definition
  "inverse :: rat \<Rightarrow> rat" is rat_inverse_raw by (force simp add: mult_commute)

definition
  divide_rat_def: "q / r = q * inverse (r::rat)"

instance proof
  fix q :: rat
  assume "q \<noteq> 0"
  then show "inverse q * q = 1"
    by partiality_descending auto
next
  fix q r :: rat
  show "q / r = q * inverse r" by (simp add: divide_rat_def)
next
  show "inverse 0 = (0::rat)" by partiality_descending auto
qed

end

instantiation rat :: linorder
begin

instance proof
  fix q r s :: rat
  {
    assume "q \<le> r" and "r \<le> s"
    then show "q \<le> s"
    proof (partiality_descending, auto simp add: mult_assoc[symmetric])
      fix a b c d e f :: int
      assume nz: "b \<noteq> 0" "d \<noteq> 0" "f \<noteq> 0"
      then have d2: "d * d > 0"
        by (metis linorder_neqE_linordered_idom mult_eq_0_iff not_square_less_zero)
      assume le: "a * d * b * d \<le> c * b * b * d" "c * f * d * f \<le> e * d * d * f"
      then have a: "a * d * b * d * f * f \<le> c * b * b * d * f * f" using nz(3)
        by (metis linorder_le_cases mult_right_mono mult_right_mono_neg)
      have "c * f * d * f * b * b \<le> e * d * d * f * b * b" using nz(1) le
        by (metis linorder_le_cases mult_right_mono mult_right_mono_neg)
      then have "a * f * b * f * (d * d) \<le> e * b * b * f * (d * d)" using a
        by (simp add: algebra_simps)
      then show "a * f * b * f \<le> e * b * b * f" using d2
        by (metis leD linorder_le_less_linear mult_strict_right_mono)
    qed
  next
    assume "q \<le> r" and "r \<le> q"
    then show "q = r"
      apply (partiality_descending, auto)
      apply (case_tac "b > 0", case_tac [!] "ba > 0")
      apply simp_all
      done
  next
    show "q \<le> q" by partiality_descending auto
    show "(q < r) = (q \<le> r \<and> \<not> r \<le> q)"
      unfolding less_rat_def
      by partiality_descending (auto simp add: le_less mult_commute)
    show "q \<le> r \<or> r \<le> q"
      by partiality_descending (auto simp add: mult_commute linorder_linear)
  }
qed

end

instance rat :: archimedean_field
proof
  fix q r s :: rat
  show "q \<le> r ==> s + q \<le> s + r"
  proof (partiality_descending, auto simp add: algebra_simps, simp add: mult_assoc[symmetric])
    fix a b c d e :: int
    assume "e \<noteq> 0"
    then have e2: "e * e > 0"
      by (metis linorder_neqE_linordered_idom mult_eq_0_iff not_square_less_zero)
      assume "a * b * d * d \<le> b * b * c * d"
      then show "a * b * d * d * e * e * e * e \<le> b * b * c * d * e * e * e * e"
        using e2 by (metis comm_mult_left_mono mult_commute linorder_le_cases
          mult_left_mono_neg)
    qed
  show "q < r ==> 0 < s ==> s * q < s * r" unfolding less_rat_def
    proof (partiality_descending, auto simp add: algebra_simps, simp add: mult_assoc[symmetric])
    fix a b c d e f :: int
    assume a: "e \<noteq> 0" "f \<noteq> 0" "0 \<le> e * f" "a * b * d * d \<le> b * b * c * d"
    have "a * b * d * d * (e * f) \<le> b * b * c * d * (e * f)" using a
      by (simp add: mult_right_mono)
    then show "a * b * d * d * e * f * f * f \<le> b * b * c * d * e * f * f * f"
      by (simp add: mult_assoc[symmetric]) (metis a(3) comm_mult_left_mono
        mult_commute mult_left_mono_neg zero_le_mult_iff)
  qed
  show "\<exists>z. r \<le> of_int z"
    unfolding of_int_rat
  proof (partiality_descending, auto)
    fix a b :: int
    assume "b \<noteq> 0"
    then have "a * b \<le> (a div b + 1) * b * b"
      by (metis mult_commute div_mult_self1_is_id less_int_def linorder_le_cases zdiv_mono1 zdiv_mono1_neg zle_add1_eq_le)
    then show "\<exists>z\<Colon>int. a * b \<le> z * b * b" by auto
  qed
qed
*)

end
