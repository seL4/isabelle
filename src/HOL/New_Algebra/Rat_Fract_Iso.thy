section \<open>The Isomorphism \<open>int fract \<cong> rat\<close> and Transfer of Irreducibility to \<open>rat poly\<close>\<close>

theory Rat_Fract_Iso
  imports Ring_Iso_Irreducible "HOL-Computational_Algebra.Polynomial_Factorial"
begin

text \<open>
  Isabelle's @{typ rat} and the field of fractions @{typ "int fract"} of the integers are
  both built as \<open>(int \<times> int)\<close> quotients with the same \<open>Fract\<close> constructor and identical
  arithmetic. We build the canonical ring isomorphism @{term fract_to_rat} between them and use it,
  to transfer irreducibility of an integer polynomial to the corresponding @{typ "rat poly"}.

  This is reusable infrastructure for any development that needs irreducibility of a rational 
  polynomial obtained from an integer one (e.g.\ via Eisenstein's criterion).
\<close>

subsection \<open>The isomorphism \<open>int fract \<rightarrow> rat\<close>\<close>

definition fract_to_rat :: "int fract \<Rightarrow> rat" where
  "fract_to_rat x = Rat.Fract (fst (quot_of_fract x)) (snd (quot_of_fract x))"

text \<open>The key bridge: on the common \<open>Fract\<close> representation the map is the identity.\<close>
lemma fract_to_rat_Fract:
  assumes "b \<noteq> 0"
  shows "fract_to_rat (Fraction_Field.Fract a b) = Rat.Fract a b"
proof -
  obtain a' b' where q: "quot_of_fract (Fraction_Field.Fract a b) = (a', b')" by fastforce
  then have ff: "fract_to_rat (Fraction_Field.Fract a b) = Rat.Fract a' b'"
    by (simp add: fract_to_rat_def)
  have b': "b' \<noteq> 0" using q snd_quot_of_fract_nonzero[of "Fraction_Field.Fract a b"] by simp
  have "Fraction_Field.Fract a' b' = Fraction_Field.Fract a b"
    using Fract_quot_of_fract[of "Fraction_Field.Fract a b"] q by simp
  then show ?thesis
    by (simp add: assms b' eq_fract(1) eq_rat(1) ff)
qed

lemma fract_to_rat_0: "fract_to_rat 0 = 0"
  by (metis Zero_fract_def fract_to_rat_Fract Rat.Zero_rat_def zero_neq_one)

lemma fract_to_rat_1: "fract_to_rat 1 = 1"
  by (metis One_fract_def fract_to_rat_Fract Rat.One_rat_def zero_neq_one)

lemma fract_to_rat_add: "fract_to_rat (x + y) = fract_to_rat x + fract_to_rat y"
proof -
  obtain a b where x: "x = Fraction_Field.Fract a b" "b \<noteq> 0" by (metis Fract_cases)
  obtain c d where y: "y = Fraction_Field.Fract c d" "d \<noteq> 0" by (metis Fract_cases)
  have "x + y = Fraction_Field.Fract (a*d + c*b) (b*d)" using x y by simp
  then show ?thesis
    by (simp add: fract_to_rat_Fract x y)
qed

lemma fract_to_rat_mult: "fract_to_rat (x * y) = fract_to_rat x * fract_to_rat y"
proof -
  obtain a b where x: "x = Fraction_Field.Fract a b" "b \<noteq> 0" by (metis Fract_cases)
  obtain c d where y: "y = Fraction_Field.Fract c d" "d \<noteq> 0" by (metis Fract_cases)
  have "x * y = Fraction_Field.Fract (a*c) (b*d)" using x y by simp
  then show ?thesis
    by (simp add: fract_to_rat_Fract x y) 
qed

lemma fract_to_rat_diff: "fract_to_rat (x - y) = fract_to_rat x - fract_to_rat y"
  by (metis eq_diff_eq fract_to_rat_add)

lemma fract_to_rat_surj: "surj fract_to_rat"
proof (rule surjI)
  fix y 
  show "fract_to_rat (Fraction_Field.Fract (fst (quotient_of y)) (snd (quotient_of y))) = y"
    by (metis Fract_quotient_of fract_to_rat_Fract less_irrefl quotient_of_denom_pos')
qed

lemma fract_to_rat_eq_0: "fract_to_rat z = 0 \<Longrightarrow> z = 0"
proof (rule ccontr)
  assume z0: "fract_to_rat z = 0" and zne: "z \<noteq> 0"
  have "fract_to_rat z * fract_to_rat (inverse z) = fract_to_rat (z * inverse z)"
    by (simp add: fract_to_rat_mult)
  then show False
    by (simp add: fract_to_rat_1 z0 zne)
qed

lemma fract_to_rat_inj: "inj fract_to_rat"
proof (rule injI)
  fix x y assume "fract_to_rat x = fract_to_rat y"
  then show "x = y"
    by (metis fract_to_rat_diff fract_to_rat_eq_0 right_minus_eq)
qed

lemma fract_to_rat_bij: "bij fract_to_rat"
  using fract_to_rat_inj fract_to_rat_surj by (rule bijI)

lemma fract_to_rat_to_fract: "fract_to_rat (to_fract n) = of_int n"
  by (simp add: fract_to_rat_Fract of_int_rat to_fract_def)


subsection \<open>The induced isomorphism on polynomials\<close>

lemma fract_to_rat_sum: "fract_to_rat (sum f A) = (\<Sum>x\<in>A. fract_to_rat (f x))"
  by (cases "finite A", induction A rule: finite_induct)
     (simp_all add: fract_to_rat_0 fract_to_rat_add)

lemma mfr_0 [simp]: "map_poly fract_to_rat 0 = 0" 
  
  by (simp add: fract_to_rat_0)
lemma mfr_1 [simp]: "map_poly fract_to_rat 1 = 1" 
  
  by (simp add: map_poly_1' fract_to_rat_1)

lemma mfr_mult:
  "map_poly fract_to_rat (p * q) = map_poly fract_to_rat p * map_poly fract_to_rat q"
  by (intro poly_eqI)
     (simp_all add: coeff_map_poly fract_to_rat_0 fract_to_rat_sum fract_to_rat_mult coeff_mult)

lemma inv_fract_to_rat_0: "inv fract_to_rat 0 = 0"
  using fract_to_rat_0 fract_to_rat_inj by (metis inv_f_f)

lemma mfr_bij: "bij (map_poly fract_to_rat)"
proof (rule bijI)
  let ?g = "inv fract_to_rat"
  have gf: "?g \<circ> fract_to_rat = id" using fract_to_rat_inj by (simp add: inv_o_cancel)
  have fg: "fract_to_rat \<circ> ?g = id" using fract_to_rat_surj by (simp add: surj_iff)
  have "map_poly ?g (map_poly fract_to_rat p) = p" for p
    by (simp add: fract_to_rat_0 gf inv_fract_to_rat_0 map_poly_map_poly)
  then show "inj (map_poly fract_to_rat)" by (metis injI)
  have "map_poly fract_to_rat (map_poly ?g p) = p" for p
    by (simp add: fg fract_to_rat_0 inv_fract_to_rat_0 map_poly_map_poly)
  then show "surj (map_poly fract_to_rat)" by (metis surjI)
qed


subsection \<open>Transfer of irreducibility from \<open>int poly\<close> to \<open>rat poly\<close>\<close>

text \<open>An irreducible primitive integer polynomial of positive degree stays irreducible over
  the rationals.  (Gauss bridge to @{typ "int fract"}, then transport along the isomorphism.)\<close>
theorem irreducible_int_imp_rat:
  fixes p :: "int poly"
  assumes irr: "irreducible p" and deg: "degree p \<noteq> 0" and cont: "content p = 1"
  shows "irreducible (map_poly of_int p :: rat poly)"
proof -
  have irr_ff: "irreducible (map_poly to_fract p :: int fract poly)"
    using irr deg cont by (subst (asm) nonconst_poly_irreducible_iff) auto
  have "irreducible (map_poly fract_to_rat (map_poly to_fract p))"
    using ring_iso_irreducible[OF mfr_mult mfr_1 mfr_0 mfr_bij] irr_ff by blast
  also have "map_poly fract_to_rat (map_poly to_fract p) = map_poly of_int p"
    by (simp add: coeff_map_poly fract_to_rat_0 fract_to_rat_to_fract poly_eqI)
  finally show ?thesis .
qed

end
